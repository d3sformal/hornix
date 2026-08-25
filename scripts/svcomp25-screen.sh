#!/usr/bin/env bash
#
# Screen SV-COMP 2025 reachability tasks and execute Hornix only for tasks
# whose CHC conversion succeeds. Worker processes do not share output files;
# Hornix itself creates unique temporary files for Clang and the solver.

set -uo pipefail

safe_log_name() {
    printf '%s' "${1//\//__}" | tr -c '[:alnum:]_.-' '_'
}

worker_screen() {
    local suite_dir="$1" hornix="$2" theory="$3" timeout_seconds="$4" stderr_dir="$5"
    local task="$6" source="$7" expected="$8"
    local error_file message exit_code
    error_file="${stderr_dir}/$(safe_log_name "${task}").screen.log"

    timeout "${timeout_seconds}" "${hornix}" --integer-theory "${theory}" --print-chc "${suite_dir}/${source}" \
        > /dev/null 2> "${error_file}"
    exit_code=$?
    if [[ ${exit_code} -eq 0 ]]; then
        rm -f "${error_file}"
        printf '%s\t%s\t%s\tTRANSLATABLE\t0\t\n' "${task}" "${source}" "${expected}"
    else
        message="$(head -n 1 "${error_file}" | tr '\t\n' ' ')"
        [[ -n "${message}" ]] || message="no diagnostic emitted"
        printf '%s\t%s\t%s\tREJECTED\t%s\t%s\n' "${task}" "${source}" "${expected}" "${exit_code}" "${message}"
    fi
}

worker_solve() {
    local suite_dir="$1" hornix="$2" theory="$3" timeout_seconds="$4" stderr_dir="$5"
    local task="$6" source="$7" expected="$8"
    local error_file output actual exit_code message status
    error_file="${stderr_dir}/$(safe_log_name "${task}").solve.log"

    output="$(timeout "${timeout_seconds}" "${hornix}" --integer-theory "${theory}" "${suite_dir}/${source}" 2> "${error_file}")"
    exit_code=$?
    actual="$(awk 'NR == 1 {print tolower($1)}' <<< "${output}")"
    case "${actual}" in
        sat) actual=true ;;
        unsat) actual=false ;;
    esac

    if [[ ${exit_code} -eq 0 && ( "${actual}" == true || "${actual}" == false ) ]]; then
        if [[ "${actual}" == "${expected}" ]]; then
            status=MATCH
        else
            status=MISMATCH
        fi
        rm -f "${error_file}"
        message=""
    elif [[ ${exit_code} -eq 0 ]]; then
        status=ERROR
        message="$(head -n 1 <<< "${output}" | tr '\t\n' ' ')"
        [[ -n "${message}" ]] || message="no result emitted"
    else
        status=ERROR
        message="$(head -n 1 "${error_file}" | tr '\t\n' ' ')"
        [[ -n "${message}" ]] || message="no diagnostic emitted"
    fi
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "${task}" "${source}" "${expected}" "${actual:-no-result}" "${status}" "${exit_code}" "${message}"
}

if [[ "${1:-}" == --worker-screen ]]; then
    shift
    worker_screen "$@"
    exit 0
fi
if [[ "${1:-}" == --worker-solve ]]; then
    shift
    worker_solve "$@"
    exit 0
fi

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
suite_dir="${project_dir}/sv-benchmarks-svcomp25"
hornix="${project_dir}/build/src/hornix"
theory="bitvectors"
timeout_seconds=30
jobs=4
limit=100
resume_dir=""
top_directories=()

usage() {
    cat <<'EOF'
Usage: scripts/svcomp25-screen.sh [options]

Screen SV-COMP 2025 C reachability tasks and execute Hornix only for the
translatable candidates. The default is a visible 100-task preview.

Options:
  --all                    Process every eligible task definition.
  --limit N                Process at most N eligible task definitions (default: 100).
  --jobs N                 Number of concurrent Hornix workers (default: 4).
  --timeout SECONDS        Per Hornix invocation timeout (default: 30).
  --integer-theory THEORY  Hornix theory: int or bitvectors (default: bitvectors).
  --top-dir NAME           Restrict to a top-level directory below c/; repeatable.
  --resume DIR             Continue an interrupted run directory.
  --suite DIR              Path to the unpacked SV-COMP 2025 benchmark suite.
  --hornix PATH            Path to the Hornix executable.
  -h, --help               Show this help.

Results are written to results/svcomp25-<timestamp>/:
  selected.tsv             selected eligible task definitions
  rejected.tsv             compiler/translation and solver failures
  translatable.tsv         tasks accepted by Hornix's CHC conversion
  results.tsv              solver results and expected-verdict comparison
  directory-summary.tsv    translation and verdict counts per source directory
  *-joblog.tsv             GNU Parallel job log for each phase
  stderr/                  one error log per rejected or failed task

The script supports only scalar, single-file C task definitions with the
standard unreach-call.prp property. This is a diagnostic baseline, not an
official SV-COMP reproduction.
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --all) limit=0; shift ;;
        --limit) limit="${2:?missing value for --limit}"; shift 2 ;;
        --jobs) jobs="${2:?missing value for --jobs}"; shift 2 ;;
        --timeout) timeout_seconds="${2:?missing value for --timeout}"; shift 2 ;;
        --integer-theory) theory="${2:?missing value for --integer-theory}"; shift 2 ;;
        --top-dir) top_directories+=("${2:?missing value for --top-dir}"); shift 2 ;;
        --resume) resume_dir="${2:?missing value for --resume}"; shift 2 ;;
        --suite) suite_dir="${2:?missing value for --suite}"; shift 2 ;;
        --hornix) hornix="${2:?missing value for --hornix}"; shift 2 ;;
        -h|--help) usage; exit 0 ;;
        *) echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
    esac
done

if [[ ! -x "${hornix}" || ! -d "${suite_dir}/c" || "${theory}" != int && "${theory}" != bitvectors ]]; then
    echo "Check --hornix, --suite, and --integer-theory arguments." >&2
    exit 2
fi
if ! [[ "${limit}" =~ ^[0-9]+$ && "${jobs}" =~ ^[1-9][0-9]*$ && "${timeout_seconds}" =~ ^[1-9][0-9]*$ ]]; then
    echo "--limit must be non-negative; --jobs and --timeout must be positive integers." >&2
    exit 2
fi
if ! command -v parallel > /dev/null; then
    echo "GNU Parallel is required; install the 'parallel' package first." >&2
    exit 2
fi

read_task_metadata() {
    # Read many YAML files in one Awk process.  Starting a separate process for
    # every task definition made the initial selection noticeably slower than
    # the actual Hornix screening.
    xargs -0 -r awk '
        function emit() {
            if (input != "" && (expected == "true" || expected == "false"))
                print file "\t" input "\t" expected
        }
        FNR == 1 {
            if (file != "") emit()
            file = FILENAME
            input = ""
            expected = ""
            wanted = 0
        }
        $1 == "input_files:" && NF == 2 {
            input = $2
            quote = sprintf("%c", 39)
            if (substr(input, 1, 1) == quote || substr(input, 1, 1) == "\"")
                input = substr(input, 2)
            if (substr(input, length(input), 1) == quote || substr(input, length(input), 1) == "\"")
                input = substr(input, 1, length(input) - 1)
            next
        }
        /property_file:[[:space:]]+.*\/unreach-call\.prp[[:space:]]*$/ {
            wanted = 1
            next
        }
        wanted && /expected_verdict:[[:space:]]+/ {
            expected = $2
            wanted = 0
        }
        END { if (file != "") emit() }
    '
}

if [[ -n "${resume_dir}" ]]; then
    run_dir="$(cd "${resume_dir}" && pwd)"
    [[ -f "${run_dir}/selected.tsv" ]] || { echo "No selected.tsv in ${run_dir}" >&2; exit 2; }
    echo "Resuming ${run_dir} with ${jobs} workers."
else
    run_dir="${project_dir}/results/svcomp25-$(date +%Y%m%d-%H%M%S)"
    mkdir -p "${run_dir}"
fi
stderr_dir="${run_dir}/stderr"
mkdir -p "${stderr_dir}"
scratch_dir="$(mktemp -d "${TMPDIR:-/tmp}/hornix-svcomp25.XXXXXX")"
trap 'rm -rf "${scratch_dir}"' EXIT

selected="${run_dir}/selected.tsv"
rejected="${run_dir}/rejected.tsv"
translatable="${run_dir}/translatable.tsv"
results="${run_dir}/results.tsv"
[[ -f "${rejected}" ]] || printf 'task_definition\tsource\tstage\texit_code\tmessage\n' > "${rejected}"
[[ -f "${translatable}" ]] || printf 'task_definition\tsource\texpected_verdict\n' > "${translatable}"
[[ -f "${results}" ]] || printf 'task_definition\tsource\texpected_verdict\thornix_result\tstatus\n' > "${results}"

if [[ -z "${resume_dir}" ]]; then
    printf 'task_definition\tsource\texpected_verdict\n' > "${selected}"
    eligible_count=0
    while IFS=$'\t' read -r task_definition input_file expected; do
        # Do not stop reading early: that would close the process-substitution
        # pipe and make the upstream Awk process report SIGPIPE.
        [[ "${limit}" -ne 0 && "${eligible_count}" -ge "${limit}" ]] && continue
        source_file="$(dirname "${task_definition}")/${input_file}"
        [[ -f "${source_file}" && "${source_file}" == *.c ]] || continue
        relative_task="${task_definition#${suite_dir}/}"
        relative_source="${source_file#${suite_dir}/}"
        printf '%s\t%s\t%s\n' "${relative_task}" "${relative_source}" "${expected}" >> "${selected}"
        ((eligible_count += 1))
    done < <(
        if [[ ${#top_directories[@]} -eq 0 ]]; then
            find "${suite_dir}/c" -type f -name '*.yml' -print0
        else
            for directory in "${top_directories[@]}"; do
                [[ -d "${suite_dir}/c/${directory}" ]] || {
                    echo "Ignoring nonexistent directory: c/${directory}" >&2
                    continue
                }
                find "${suite_dir}/c/${directory}" -type f -name '*.yml' -print0
            done
        fi | LC_ALL=C sort -z | read_task_metadata
    )
fi

screen_done="${scratch_dir}/screen-done.tsv"
awk -F '\t' 'FNR > 1 { print $1 }' "${translatable}" "${rejected}" | LC_ALL=C sort -u > "${screen_done}"
pending_screen="${scratch_dir}/pending-screen.tsv"
awk -F '\t' 'FILENAME == ARGV[1] { done[$1] = 1; next } FNR > 1 && !($1 in done) { print }' "${screen_done}" "${selected}" > "${pending_screen}"
pending_screen_count="$(wc -l < "${pending_screen}")"
echo "Stage 1/2: ${pending_screen_count} pending translations with ${jobs} workers."

if [[ "${pending_screen_count}" -gt 0 ]]; then
    screen_new="${scratch_dir}/screen-new.tsv"
    parallel --will-cite --jobs "${jobs}" --line-buffer --bar \
        --joblog "${run_dir}/screen-joblog.tsv" --colsep '\t' \
        bash "$0" --worker-screen "${suite_dir}" "${hornix}" "${theory}" "${timeout_seconds}" "${stderr_dir}" {1} {2} {3} \
        :::: "${pending_screen}" > "${screen_new}"
    while IFS=$'\t' read -r task source expected status exit_code message; do
        if [[ "${status}" == TRANSLATABLE ]]; then
            printf '%s\t%s\t%s\n' "${task}" "${source}" "${expected}" >> "${translatable}"
        else
            printf '%s\t%s\tscreen\t%s\t%s\n' "${task}" "${source}" "${exit_code}" "${message}" >> "${rejected}"
        fi
    done < "${screen_new}"
fi

solve_done="${scratch_dir}/solve-done.tsv"
awk -F '\t' 'FNR > 1 { print $1 }' "${results}" | LC_ALL=C sort -u > "${solve_done}"
pending_solve="${scratch_dir}/pending-solve.tsv"
awk -F '\t' 'FILENAME == ARGV[1] { done[$1] = 1; next } FNR > 1 && !($1 in done) { print }' "${solve_done}" "${translatable}" > "${pending_solve}"
pending_solve_count="$(wc -l < "${pending_solve}")"
echo "Stage 2/2: ${pending_solve_count} pending solver runs with ${jobs} workers."

if [[ "${pending_solve_count}" -gt 0 ]]; then
    solve_new="${scratch_dir}/solve-new.tsv"
    parallel --will-cite --jobs "${jobs}" --line-buffer --bar \
        --joblog "${run_dir}/solve-joblog.tsv" --colsep '\t' \
        bash "$0" --worker-solve "${suite_dir}" "${hornix}" "${theory}" "${timeout_seconds}" "${stderr_dir}" {1} {2} {3} \
        :::: "${pending_solve}" > "${solve_new}"
    while IFS=$'\t' read -r task source expected actual status exit_code message; do
        printf '%s\t%s\t%s\t%s\t%s\n' "${task}" "${source}" "${expected}" "${actual}" "${status}" >> "${results}"
        if [[ "${status}" == ERROR ]]; then
            printf '%s\t%s\tsolve\t%s\t%s\n' "${task}" "${source}" "${exit_code}" "${message}" >> "${rejected}"
        fi
    done < "${solve_new}"
fi

directory_events="${scratch_dir}/directory-events.tsv"
awk -F '\t' 'FNR > 1 { split($2, parts, "/"); print parts[2] "\tselected" }' "${selected}" > "${directory_events}"
awk -F '\t' 'FNR > 1 { split($2, parts, "/"); print parts[2] "\ttranslatable" }' "${translatable}" >> "${directory_events}"
awk -F '\t' 'FNR > 1 && $3 == "screen" { split($2, parts, "/"); print parts[2] "\tscreen_rejected" }' "${rejected}" >> "${directory_events}"
awk -F '\t' 'FNR > 1 { split($2, parts, "/"); print parts[2] "\t" tolower($5) }' "${results}" >> "${directory_events}"
{
    printf 'directory\tselected\ttranslatable\tscreen_rejected\tmatches\tmismatches\tsolver_errors\n'
    awk -F '\t' '
        { counts[$1 SUBSEP $2] += 1; directories[$1] = 1 }
        function count(directory, label) { return counts[directory SUBSEP label] + 0 }
        END {
            for (directory in directories) {
                printf "%s\t%d\t%d\t%d\t%d\t%d\t%d\n", directory,
                    count(directory, "selected"), count(directory, "translatable"),
                    count(directory, "screen_rejected"), count(directory, "match"),
                    count(directory, "mismatch"), count(directory, "error")
            }
        }
    ' "${directory_events}" | LC_ALL=C sort
} > "${run_dir}/directory-summary.tsv"

echo "Complete. Results: ${run_dir}"
