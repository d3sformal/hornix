#!/usr/bin/env bash
#
# Run a reproducible SV-COMP violation-witness campaign. Each selected
# expected-false unreach-call task is first analysed by Hornix and every
# produced witness is then independently validated by CPAchecker.

set -uo pipefail

safe_name() {
    printf '%s' "${1//\//__}" | tr -c '[:alnum:]_.-' '_'
}

now_millis() {
    # Durations must not depend on the wall clock: NTP or a system upgrade can
    # adjust it while a campaign is running. Python's monotonic clock is also
    # available on the Ubuntu environments used for SV-COMP experiments.
    python3 -c 'import time; print(time.monotonic_ns() // 1_000_000)'
}

worker_run() {
    local suite_dir="$1" hornix="$2" cpachecker="$3" solver="$4" solver_dir="$5" solver_args="$6"
    local hornix_timeout="$7" validation_timeout="$8" run_dir="$9"
    local key="${10}" task="${11}" source="${12}" property="${13}" model="${14}"
    local witness hornix_log cpa_log cpa_output source_path property_path hornix_output hornix_exit hornix_result
    local cpa_output_text cpa_exit cpa_result status hornix_start hornix_ms cpa_start cpa_ms machine_model

    # GNU Parallel omits an empty literal command argument.  The parent uses
    # this marker for optional solver settings so the remaining task columns
    # always retain their positions.
    [[ "${solver_dir}" == "__HORNIX_EMPTY__" ]] && solver_dir=""
    [[ "${solver_args}" == "__HORNIX_EMPTY__" ]] && solver_args=""

    witness="${run_dir}/witnesses/${key}.witness.yml"
    hornix_log="${run_dir}/logs/${key}.hornix.log"
    cpa_log="${run_dir}/logs/${key}.cpachecker.log"
    cpa_output="${run_dir}/cpachecker/${key}"
    source_path="${suite_dir}/${source}"
    property_path="${suite_dir}/${property}"

    local -a solver_options=(--solver "${solver}")
    [[ -n "${solver_dir}" ]] && solver_options+=(--solver-dir "${solver_dir}")
    [[ -n "${solver_args}" ]] && solver_options+=(--solver-args "${solver_args}")

    hornix_start="$(now_millis)"
    hornix_output="$(timeout --signal=TERM --kill-after=30s "${hornix_timeout}s" "${hornix}" \
        --integer-theory bitvectors --data-model "${model}" --property "${property_path}" \
        --witness-format 2.1 --witness-output "${witness}" "${solver_options[@]}" "${source_path}" 2>&1)"
    hornix_exit=$?
    hornix_ms="$(( $(now_millis) - hornix_start ))"
    printf '%s\n' "${hornix_output}" > "${hornix_log}"
    hornix_result="$(awk 'NR == 1 {print tolower($1)}' <<< "${hornix_output}")"
    cpa_result="NOT_RUN"
    cpa_exit="-"
    cpa_ms=0
    status="HORNIX_ERROR"

    if [[ ${hornix_exit} -eq 0 && "${hornix_result}" == "unsat" && -s "${witness}" ]]; then
        mkdir -p "${cpa_output}"
        machine_model=--64
        [[ "${model}" == "ILP32" ]] && machine_model=--32
        cpa_start="$(now_millis)"
        cpa_output_text="$(cd "${cpa_output}" && timeout --signal=TERM --kill-after=30s "${validation_timeout}s" \
            "${cpachecker}" --violation-witness-validation "${machine_model}" --witness "${witness}" \
            --spec "${property_path}" "${source_path}" 2>&1)"
        cpa_exit=$?
        cpa_ms="$(( $(now_millis) - cpa_start ))"
        printf '%s\n' "${cpa_output_text}" > "${cpa_log}"
        if [[ ${cpa_exit} -eq 0 ]] && grep -Fq 'Verification result: FALSE' <<< "${cpa_output_text}"; then
            cpa_result=FALSE
            status=VALIDATED
        else
            cpa_result="$(awk '/Verification result:/ {print $3; exit}' <<< "${cpa_output_text}")"
            [[ -n "${cpa_result}" ]] || cpa_result="ERROR_${cpa_exit}"
            status=WITNESS_INVALID
        fi
    elif [[ ${hornix_exit} -eq 124 ]]; then
        hornix_result=TIMEOUT
        status=TIMEOUT
    elif [[ ${hornix_exit} -eq 0 && "${hornix_result}" == "unsat" ]]; then
        status=WITNESS_MISSING
    elif [[ ${hornix_exit} -eq 0 && "${hornix_result}" == "sat" ]]; then
        status=SAT
    elif [[ ${hornix_exit} -eq 0 ]]; then
        hornix_result="${hornix_result:-NO_RESULT}"
        status=NO_RESULT
    else
        hornix_result="${hornix_result:-ERROR_${hornix_exit}}"
    fi

    local outcome="${run_dir}/outcomes/${key}.tsv"
    local temporary_outcome="${outcome}.tmp.$$"
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "${key}" "${task}" "${source}" "${model}" "${hornix_result}" "${hornix_exit}" "${hornix_ms}" \
        "${cpa_result}" "${cpa_exit}" "${cpa_ms}" "${status}" > "${temporary_outcome}"
    mv "${temporary_outcome}" "${outcome}"
}

if [[ "${1:-}" == "--worker-run" ]]; then
    shift
    worker_run "$@"
    exit 0
fi

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
suite_dir="${project_dir}/sv-benchmarks-svcomp25"
hornix="${project_dir}/build/src/hornix"
cpachecker="cpachecker"
solver="z3"
solver_dir=""
solver_args=""
hornix_timeout=900
validation_timeout=90
jobs=1
limit=100
label=""
resume_dir=""
top_directories=(bitvector bitvector-regression loop-simple loops recursive recursive-simple)
top_dir_overridden=false

usage() {
    cat <<'EOF'
Usage: scripts/svcomp-witness-campaign.sh [options]

Run expected-false, single-file C unreach-call tasks through Hornix and
validate every generated violation witness with CPAchecker.  The default is a
100-task preview from the scalar categories screened as most relevant to
Hornix.  Use --all for the whole selected category set.

Options:
  --all                    Process every eligible task in the selected directories.
  --limit N                Process at most N eligible tasks (default: 100).
  --jobs N                 Concurrent task workers (default: 1).
  --timeout SECONDS        Per Hornix run, wall-time limit (default: 900).
  --validation-timeout N   Per CPAchecker validation, wall-time limit (default: 90).
  --solver COMMAND         Horn-clause solver passed to Hornix (default: z3).
  --solver-dir DIR         Directory containing COMMAND, passed to Hornix.
  --solver-args ARGS       Extra arguments passed verbatim to COMMAND by Hornix.
  --top-dir NAME           Restrict selection to c/NAME; repeatable.
  --label NAME             Include NAME in the result-directory name.
  --resume DIR             Continue a previous campaign directory.
  --suite DIR              Unpacked SV-COMP benchmark suite.
  --hornix PATH            Hornix executable (default: build/src/hornix).
  --cpachecker PATH        CPAchecker executable (default: cpachecker on PATH).
  -h, --help               Show this help.

Each campaign creates results/<input-dir-name>-*/ containing:
  selected.tsv             deterministic candidate list
  results.tsv              Hornix and CPAchecker outcomes plus elapsed milliseconds
  status-summary.tsv       counts of validated witnesses, timeouts, and failures
  solver-summary.tsv       counts by Hornix result
  directory-summary.tsv    validated and failed tasks grouped by source directory
  timing-summary.tsv       aggregate Hornix and CPAchecker wall-clock timings
  configuration.tsv        full campaign configuration
  witnesses/, logs/, cpachecker/, outcomes/

The script returns success only when every selected task produces a witness
accepted by CPAchecker. Durations use a monotonic clock. A campaign is
diagnostic, not an official SV-COMP reproduction: timeout is wall time and no
memory or CPU-core limit is imposed.
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --all) limit=0; shift ;;
        --limit) limit="${2:?missing value for --limit}"; shift 2 ;;
        --jobs) jobs="${2:?missing value for --jobs}"; shift 2 ;;
        --timeout) hornix_timeout="${2:?missing value for --timeout}"; shift 2 ;;
        --validation-timeout) validation_timeout="${2:?missing value for --validation-timeout}"; shift 2 ;;
        --solver) solver="${2:?missing value for --solver}"; shift 2 ;;
        --solver-dir) solver_dir="${2:?missing value for --solver-dir}"; shift 2 ;;
        --solver-args) solver_args="${2:?missing value for --solver-args}"; shift 2 ;;
        --top-dir)
            if [[ "${top_dir_overridden}" == false ]]; then
                top_directories=()
                top_dir_overridden=true
            fi
            top_directories+=("${2:?missing value for --top-dir}")
            shift 2
            ;;
        --label) label="${2:?missing value for --label}"; shift 2 ;;
        --resume) resume_dir="${2:?missing value for --resume}"; shift 2 ;;
        --suite) suite_dir="${2:?missing value for --suite}"; shift 2 ;;
        --hornix) hornix="${2:?missing value for --hornix}"; shift 2 ;;
        --cpachecker) cpachecker="${2:?missing value for --cpachecker}"; shift 2 ;;
        -h|--help) usage; exit 0 ;;
        *) echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
    esac
done

if ! [[ "${limit}" =~ ^[0-9]+$ && "${jobs}" =~ ^[1-9][0-9]*$ &&
          "${hornix_timeout}" =~ ^[1-9][0-9]*$ && "${validation_timeout}" =~ ^[1-9][0-9]*$ ]]; then
    echo "--limit must be non-negative; --jobs and both timeouts must be positive integers." >&2
    exit 2
fi
if [[ -z "${solver}" || ! -x "${hornix}" || ! -d "${suite_dir}/c" ]]; then
    echo "Check --solver, --hornix, and --suite." >&2
    exit 2
fi
# Worker processes change into a per-task directory for CPAchecker. Keep all
# benchmark paths absolute so the program and property remain addressable.
suite_dir="$(cd "${suite_dir}" && pwd -P)"
if [[ -n "${solver_dir}" && ! -d "${solver_dir}" ]]; then
    echo "--solver-dir is not a directory: ${solver_dir}" >&2
    exit 2
fi
if ! command -v "${cpachecker}" > /dev/null; then
    echo "CPAchecker executable not found: ${cpachecker}" >&2
    exit 2
fi
if ! command -v parallel > /dev/null; then
    echo "GNU Parallel is required; install the 'parallel' package first." >&2
    exit 2
fi
if ! command -v python3 > /dev/null; then
    echo "Python 3 is required for monotonic duration measurement." >&2
    exit 2
fi
cpachecker="$(command -v "${cpachecker}")"

read_task_metadata() {
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

if [[ -n "${resume_dir}" ]]; then
    run_dir="$(cd "${resume_dir}" && pwd)"
    [[ -f "${run_dir}/selected.tsv" && -d "${run_dir}/outcomes" ]] || {
        echo "--resume requires selected.tsv and outcomes/ in ${run_dir}" >&2
        exit 2
    }
    echo "Resuming ${run_dir}. The current command-line solver settings are used."
else
    run_suffix="$(safe_name "${label:-${solver}}")"
    suite_name="$(safe_name "$(basename "${suite_dir}")")"
    run_dir="${project_dir}/results/${suite_name}-witness-campaign-${run_suffix}-$(date +%Y%m%d-%H%M%S)"
    mkdir -p "${run_dir}/witnesses" "${run_dir}/logs" "${run_dir}/cpachecker" "${run_dir}/outcomes"
    {
        printf 'key\tvalue\n'
        printf 'suite\t%s\nhornix\t%s\ncpachecker\t%s\nsolver\t%s\nsolver_dir\t%s\nsolver_args\t%s\n' \
            "${suite_dir}" "${hornix}" "${cpachecker}" "${solver}" "${solver_dir}" "${solver_args}"
        printf 'hornix_timeout_seconds\t%s\nvalidation_timeout_seconds\t%s\njobs\t%s\n' \
            "${hornix_timeout}" "${validation_timeout}" "${jobs}"
    } > "${run_dir}/configuration.tsv"

    scratch_dir="$(mktemp -d "${TMPDIR:-/tmp}/hornix-witness-campaign.XXXXXX")"
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

    selected="${run_dir}/selected.tsv"
    printf 'key\ttask_definition\tsource\tproperty\tdata_model\n' > "${selected}"
    count=0
    while IFS=$'\t' read -r task input property model; do
        [[ "${limit}" -ne 0 && "${count}" -ge "${limit}" ]] && continue
        task_dir="$(dirname "${task}")"
        source_file="${task_dir}/${input}"
        property_file="${task_dir}/${property}"
        [[ -f "${source_file}" && -f "${property_file}" && "${source_file}" == *.c ]] || continue
        ((count += 1))
        key="$(printf '%05d-%s' "${count}" "$(safe_name "${source_file#${suite_dir}/}")")"
        printf '%s\t%s\t%s\t%s\t%s\n' "${key}" "${task#${suite_dir}/}" \
            "${source_file#${suite_dir}/}" "${property_file#${suite_dir}/}" "${model}" >> "${selected}"
    done < "${metadata}"
fi

selected="${run_dir}/selected.tsv"
pending="$(mktemp "${TMPDIR:-/tmp}/hornix-witness-pending.XXXXXX")"
trap 'rm -rf "${scratch_dir:-}"; rm -f "${pending:-}"' EXIT
awk -F '\t' -v outcomes="${run_dir}/outcomes" '
    NR > 1 {
        command = "test -f \"" outcomes "/" $1 ".tsv\""
        if (system(command) != 0) print
    }
' "${selected}" > "${pending}"

task_count="$(( $(wc -l < "${selected}") - 1 ))"
pending_count="$(wc -l < "${pending}")"
if [[ "${task_count}" -eq 0 ]]; then
    echo "No eligible expected-false unreach-call tasks were selected." >&2
    exit 2
fi
echo "Campaign ${run_dir}: ${task_count} selected, ${pending_count} pending; solver=${solver}, jobs=${jobs}."

if [[ "${pending_count}" -gt 0 ]]; then
    # Keep empty optional arguments as explicit values: otherwise GNU Parallel
    # removes them and shifts the five TSV task fields passed to worker_run.
    worker_solver_dir="${solver_dir:-__HORNIX_EMPTY__}"
    worker_solver_args="${solver_args:-__HORNIX_EMPTY__}"
    parallel --will-cite --jobs "${jobs}" --line-buffer --bar \
        --joblog "${run_dir}/joblog.tsv" --colsep '\t' \
        bash "$0" --worker-run "${suite_dir}" "${hornix}" "${cpachecker}" "${solver}" "${worker_solver_dir}" "${worker_solver_args}" \
        "${hornix_timeout}" "${validation_timeout}" "${run_dir}" {1} {2} {3} {4} {5} \
        :::: "${pending}"
fi

results="${run_dir}/results.tsv"
printf 'key\ttask_definition\tsource\tdata_model\thornix_result\thornix_exit\thornix_ms\tcpachecker_result\tcpachecker_exit\tcpachecker_ms\tstatus\n' > "${results}"
while IFS=$'\t' read -r key task source property model; do
    [[ "${key}" == key ]] && continue
    [[ -f "${run_dir}/outcomes/${key}.tsv" ]] && cat "${run_dir}/outcomes/${key}.tsv" >> "${results}"
done < "${selected}"

printf 'status\tcount\n' > "${run_dir}/status-summary.tsv"
awk -F '\t' 'NR > 1 { count[$11] += 1 } END { for (key in count) print key "\t" count[key] }' "${results}" | LC_ALL=C sort >> "${run_dir}/status-summary.tsv"

printf 'hornix_result\tcount\n' > "${run_dir}/solver-summary.tsv"
awk -F '\t' 'NR > 1 { count[$5] += 1 } END { for (key in count) print key "\t" count[key] }' "${results}" | LC_ALL=C sort >> "${run_dir}/solver-summary.tsv"

printf 'directory\tselected\tvalidated\ttimeouts\tother\n' > "${run_dir}/directory-summary.tsv"
awk -F '\t' '
    NR > 1 {
        split($3, path, "/"); directory = path[2]
        selected[directory] += 1
        if ($11 == "VALIDATED") validated[directory] += 1
        else if ($11 == "TIMEOUT") timeouts[directory] += 1
        else other[directory] += 1
    }
    END {
        for (directory in selected)
            print directory "\t" selected[directory] "\t" (validated[directory] + 0) "\t" \
                  (timeouts[directory] + 0) "\t" (other[directory] + 0)
    }
' "${results}" | LC_ALL=C sort >> "${run_dir}/directory-summary.tsv"

printf 'stage\tcompleted\ttotal_ms\taverage_ms\tmax_ms\n' > "${run_dir}/timing-summary.tsv"
awk -F '\t' '
    NR > 1 {
        hcount += 1; hsum += $7; if ($7 > hmax) hmax = $7
        if ($10 > 0) { ccount += 1; csum += $10; if ($10 > cmax) cmax = $10 }
    }
    END {
        if (hcount) print "hornix\t" hcount "\t" hsum "\t" int(hsum / hcount) "\t" hmax
        if (ccount) print "cpachecker\t" ccount "\t" csum "\t" int(csum / ccount) "\t" cmax
    }
' "${results}" >> "${run_dir}/timing-summary.tsv"

echo "Complete. Results: ${run_dir}"
if awk -F '\t' 'NR > 1 && $11 != "VALIDATED" { exit 1 }' "${results}"; then
    exit 0
fi
exit 1
