#!/usr/bin/env bash
#
# Generate and validate a small, source-size-ordered set of SV-COMP 2025
# unreach-call violation witnesses.  The default directories were chosen from
# categories that Hornix's existing screening accepted particularly often.

set -uo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
suite_dir="${project_dir}/sv-benchmarks-svcomp25"
hornix="${project_dir}/build/src/hornix"
cpachecker="cpachecker"
solver="z3"
solver_dir=""
solver_args=""
limit=24
timeout_seconds=60
top_directories=(bitvector bitvector-regression loop-simple loops recursive recursive-simple)
top_dir_overridden=false

usage() {
    cat <<'EOF'
Usage: scripts/svcomp25-validate-witnesses.sh [options]

Generate YAML 2.1 violation witnesses with Hornix and validate them with
CPAchecker for a small set of expected-false SV-COMP 2025 unreach-call tasks.
Candidates are selected from the default supported categories, ordered by
source size, and processed sequentially.  CPAchecker runs only after Hornix
returns unsat and writes a witness.

Options:
  --limit N              Number of smallest candidates to try (default: 24).
  --timeout SECONDS      Per Hornix and CPAchecker run (default: 60).
  --top-dir NAME         Restrict selection to c/NAME; repeatable.
  --suite DIR            Unpacked SV-COMP 2025 benchmark suite.
  --hornix PATH          Hornix executable (default: build/src/hornix).
  --cpachecker PATH      CPAchecker executable (default: cpachecker on PATH).
  --solver COMMAND       Horn-clause solver passed to Hornix (default: z3).
  --solver-dir DIR       Directory containing COMMAND, passed to Hornix.
  --solver-args ARGS     Extra arguments passed verbatim to COMMAND by Hornix.
  -h, --help             Show this help.

Results are saved in results/svcomp25-witness-validation-<timestamp>/:
  selected.tsv           selected expected-false unreach-call tasks
  results.tsv            one row per task; status is strictly OK or FAIL
  configuration.tsv      Hornix, solver, and CPAchecker configuration for this run
  witnesses/             witnesses generated after Hornix reported unsat
  logs/                  complete Hornix and CPAchecker output per task
  cpachecker/            CPAchecker output directories, including reports

The script exits with status 1 if any selected task is not validated. This is
intentional: it makes the script suitable for regression testing as well as
interactive use.
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --limit) limit="${2:?missing value for --limit}"; shift 2 ;;
        --timeout) timeout_seconds="${2:?missing value for --timeout}"; shift 2 ;;
        --top-dir)
            if [[ "${top_dir_overridden}" == false ]]; then
                top_directories=()
                top_dir_overridden=true
            fi
            top_directories+=("${2:?missing value for --top-dir}")
            shift 2
            ;;
        --suite) suite_dir="${2:?missing value for --suite}"; shift 2 ;;
        --hornix) hornix="${2:?missing value for --hornix}"; shift 2 ;;
        --cpachecker) cpachecker="${2:?missing value for --cpachecker}"; shift 2 ;;
        --solver) solver="${2:?missing value for --solver}"; shift 2 ;;
        --solver-dir) solver_dir="${2:?missing value for --solver-dir}"; shift 2 ;;
        --solver-args) solver_args="${2:?missing value for --solver-args}"; shift 2 ;;
        -h|--help) usage; exit 0 ;;
        *) echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
    esac
done

if ! [[ "${limit}" =~ ^[1-9][0-9]*$ && "${timeout_seconds}" =~ ^[1-9][0-9]*$ ]]; then
    echo "--limit and --timeout must be positive integers." >&2
    exit 2
fi
if [[ -z "${solver}" ]]; then
    echo "--solver must not be empty." >&2
    exit 2
fi
if [[ -n "${solver_dir}" && ! -d "${solver_dir}" ]]; then
    echo "--solver-dir is not a directory: ${solver_dir}" >&2
    exit 2
fi
if [[ ! -x "${hornix}" || ! -d "${suite_dir}/c" ]]; then
    echo "Check --hornix and --suite." >&2
    exit 2
fi
if ! command -v "${cpachecker}" > /dev/null; then
    echo "CPAchecker executable not found: ${cpachecker}" >&2
    exit 2
fi
cpachecker="$(command -v "${cpachecker}")"

read_task_metadata() {
    # The task-definition subset used here is deliberately read with Awk so
    # that the script needs no Python or PyYAML installation on the runner.
    xargs -0 -r awk '
        function unquote(value) {
            sub(/^[[:space:]]*/, "", value)
            sub(/[[:space:]]*$/, "", value)
            if ((substr(value, 1, 1) == "\047" && substr(value, length(value), 1) == "\047") ||
                (substr(value, 1, 1) == "\"" && substr(value, length(value), 1) == "\""))
                return substr(value, 2, length(value) - 2)
            return value
        }
        function emit() {
            if (input != "" && property != "" && expected == "false" &&
                (model == "ILP32" || model == "LP64"))
                print file "\t" input "\t" property "\t" model
        }
        FNR == 1 {
            if (file != "") emit()
            file = FILENAME
            input = property = expected = model = ""
            want_expected = 0
        }
        $1 == "input_files:" && NF >= 2 { input = unquote(substr($0, index($0, ":") + 1)); next }
        $1 == "data_model:" && NF >= 2 { model = unquote($2); next }
        /property_file:[[:space:]]+.*\/unreach-call\.prp[[:space:]]*$/ {
            candidate_property = unquote(substr($0, index($0, ":") + 1))
            want_expected = 1
            next
        }
        want_expected && /expected_verdict:[[:space:]]+/ {
            if ($2 == "false") {
                property = candidate_property
                expected = $2
            }
            want_expected = 0
        }
        END { if (file != "") emit() }
    '
}

run_dir="${project_dir}/results/svcomp25-witness-validation-$(date +%Y%m%d-%H%M%S)"
mkdir -p "${run_dir}/witnesses" "${run_dir}/logs" "${run_dir}/cpachecker"
scratch_dir="$(mktemp -d "${TMPDIR:-/tmp}/hornix-witness-validation.XXXXXX")"
trap 'rm -rf "${scratch_dir}"' EXIT

configuration="${run_dir}/configuration.tsv"
printf 'key\tvalue\n' > "${configuration}"
printf 'hornix\t%s\ncpachecker\t%s\nsolver\t%s\nsolver_dir\t%s\nsolver_args\t%s\ntimeout_seconds\t%s\n' \
    "${hornix}" "${cpachecker}" "${solver}" "${solver_dir}" "${solver_args}" "${timeout_seconds}" \
    >> "${configuration}"

hornix_solver_options=(--solver "${solver}")
[[ -n "${solver_dir}" ]] && hornix_solver_options+=(--solver-dir "${solver_dir}")
[[ -n "${solver_args}" ]] && hornix_solver_options+=(--solver-args "${solver_args}")

metadata="${scratch_dir}/metadata.tsv"
{
    for directory in "${top_directories[@]}"; do
        [[ -d "${suite_dir}/c/${directory}" ]] || {
            echo "Ignoring nonexistent directory: c/${directory}" >&2
            continue
        }
        find "${suite_dir}/c/${directory}" -type f -name '*.yml' -print0
    done | LC_ALL=C sort -z | read_task_metadata
} > "${metadata}"

ranked="${scratch_dir}/ranked.tsv"
while IFS=$'\t' read -r task input property model; do
    task_dir="$(dirname "${task}")"
    source_file="${task_dir}/${input}"
    property_file="${task_dir}/${property}"
    [[ -f "${source_file}" && -f "${property_file}" && "${source_file}" == *.c ]] || continue
    bytes="$(wc -c < "${source_file}")"
    printf '%012d\t%s\t%s\t%s\t%s\n' "${bytes}" "${task#${suite_dir}/}" \
        "${source_file#${suite_dir}/}" "${property_file#${suite_dir}/}" "${model}"
done < "${metadata}" | LC_ALL=C sort -n > "${ranked}"

selected="${run_dir}/selected.tsv"
printf 'task_definition\tsource\tproperty\tdata_model\tsource_bytes\n' > "${selected}"
awk -F '\t' -v limit="${limit}" 'NR <= limit { print $2 "\t" $3 "\t" $4 "\t" $5 "\t" ($1 + 0) }' "${ranked}" >> "${selected}"

task_count="$(( $(wc -l < "${selected}") - 1 ))"
if [[ "${task_count}" -eq 0 ]]; then
    echo "No eligible expected-false unreach-call tasks were selected." >&2
    exit 2
fi

results="${run_dir}/results.tsv"
printf 'task_definition\tsource\thornix_result\tcpachecker_result\tstatus\n' > "${results}"
echo "Selected ${task_count} small expected-false tasks with solver ${solver}. Results: ${run_dir}"

index=0
while IFS=$'\t' read -r task source property model bytes; do
    [[ "${task}" == task_definition ]] && continue
    ((index += 1))
    key="$(printf '%03d' "${index}")-$(basename "${source%.c}")"
    witness="${run_dir}/witnesses/${key}.witness.yml"
    hornix_log="${run_dir}/logs/${key}.hornix.log"
    cpa_log="${run_dir}/logs/${key}.cpachecker.log"
    cpa_output="${run_dir}/cpachecker/${key}"
    source_path="${suite_dir}/${source}"
    property_path="${suite_dir}/${property}"

    hornix_output="$(timeout "${timeout_seconds}" "${hornix}" --integer-theory bitvectors \
        --data-model "${model}" --property "${property_path}" --witness-format 2.1 \
        --witness-output "${witness}" "${hornix_solver_options[@]}" "${source_path}" 2>&1)"
    hornix_exit=$?
    printf '%s\n' "${hornix_output}" > "${hornix_log}"
    hornix_result="$(awk 'NR == 1 {print tolower($1)}' <<< "${hornix_output}")"
    cpa_result="NOT_RUN"
    status=FAIL

    if [[ ${hornix_exit} -eq 0 && "${hornix_result}" == unsat && -s "${witness}" ]]; then
        mkdir -p "${cpa_output}"
        machine_model=--64
        [[ "${model}" == ILP32 ]] && machine_model=--32
        cpa_output_text="$(cd "${cpa_output}" && timeout "${timeout_seconds}" "${cpachecker}" \
            --violation-witness-validation "${machine_model}" --witness "${witness}" \
            --spec "${property_path}" "${source_path}" 2>&1)"
        cpa_exit=$?
        printf '%s\n' "${cpa_output_text}" > "${cpa_log}"
        if [[ ${cpa_exit} -eq 0 ]] && grep -Fq 'Verification result: FALSE' <<< "${cpa_output_text}"; then
            cpa_result=FALSE
            status=OK
        else
            cpa_result="$(awk '/Verification result:/ {print $3; exit}' <<< "${cpa_output_text}")"
            [[ -n "${cpa_result}" ]] || cpa_result="ERROR_${cpa_exit}"
        fi
    else
        hornix_result="${hornix_result:-ERROR_${hornix_exit}}"
    fi

    printf '%s\t%s\t%s\t%s\t%s\n' "${task}" "${source}" "${hornix_result}" "${cpa_result}" "${status}" >> "${results}"
    printf '[%d/%d] %s: Hornix=%s, CPAchecker=%s -> %s\n' \
        "${index}" "${task_count}" "${source}" "${hornix_result}" "${cpa_result}" "${status}"
done < "${selected}"

printf 'status\tcount\n' > "${run_dir}/summary.tsv"
awk -F '\t' 'NR > 1 { count[$5] += 1 } END { for (status in count) print status "\t" count[status] }' \
    "${results}" | LC_ALL=C sort >> "${run_dir}/summary.tsv"

echo "Complete. Results: ${run_dir}"
if awk -F '\t' 'NR > 1 && $5 != "OK" { exit 1 }' "${results}"; then
    exit 0
fi
exit 1
