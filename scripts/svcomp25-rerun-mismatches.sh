#!/usr/bin/env bash
#
# Re-run only verdict mismatches reported by svcomp25-screen.sh.  The source
# result table is retained unchanged; this script writes a new, self-contained
# result directory for comparison after a Hornix change.

set -uo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
screen_script="${project_dir}/scripts/svcomp25-screen.sh"
suite_dir="${project_dir}/sv-benchmarks-svcomp25"
hornix="${project_dir}/build/src/hornix"
source_run=""
theory="bitvectors"
jobs=4
timeout_seconds=60
limit=0

usage() {
    cat <<'EOF'
Usage: scripts/svcomp25-rerun-mismatches.sh --source-run DIR [options]

Re-run only rows marked MISMATCH in a prior SV-COMP screen result.  Results
are written to results/svcomp25-rerun-mismatches-<timestamp>/.

Options:
  --source-run DIR         Prior svcomp25-screen.sh result directory (required).
  --jobs N                 Number of concurrent Hornix workers (default: 4).
  --timeout SECONDS        Per Hornix invocation timeout (default: 60).
  --integer-theory THEORY  Hornix theory: int or bitvectors (default: bitvectors).
  --limit N                Re-run at most N mismatches; useful for a smoke test.
  --suite DIR              Path to the unpacked SV-COMP 2025 suite.
  --hornix PATH            Path to the Hornix executable.
  -h, --help               Show this help.

Unlike the older report, an SMT `(error ...)` response or an empty response is
recorded as ERROR, not as a verdict mismatch.
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --source-run) source_run="${2:?missing value for --source-run}"; shift 2 ;;
        --jobs) jobs="${2:?missing value for --jobs}"; shift 2 ;;
        --timeout) timeout_seconds="${2:?missing value for --timeout}"; shift 2 ;;
        --integer-theory) theory="${2:?missing value for --integer-theory}"; shift 2 ;;
        --limit) limit="${2:?missing value for --limit}"; shift 2 ;;
        --suite) suite_dir="${2:?missing value for --suite}"; shift 2 ;;
        --hornix) hornix="${2:?missing value for --hornix}"; shift 2 ;;
        -h|--help) usage; exit 0 ;;
        *) echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
    esac
done

if [[ -z "${source_run}" || ! -f "${source_run}/results.tsv" ]]; then
    echo "--source-run must name a prior result directory containing results.tsv." >&2
    exit 2
fi
if [[ ! -x "${hornix}" || ! -d "${suite_dir}/c" || ! -x "${screen_script}" ]]; then
    echo "Check --hornix, --suite, and the screen script." >&2
    exit 2
fi
if ! [[ "${jobs}" =~ ^[1-9][0-9]*$ && "${timeout_seconds}" =~ ^[1-9][0-9]*$ && "${limit}" =~ ^[0-9]+$ ]]; then
    echo "--jobs and --timeout must be positive integers; --limit must be non-negative." >&2
    exit 2
fi
if [[ "${theory}" != int && "${theory}" != bitvectors ]]; then
    echo "--integer-theory must be int or bitvectors." >&2
    exit 2
fi
if ! command -v parallel > /dev/null; then
    echo "GNU Parallel is required; install the 'parallel' package first." >&2
    exit 2
fi

source_run="$(cd "${source_run}" && pwd)"
run_dir="${project_dir}/results/svcomp25-rerun-mismatches-$(date +%Y%m%d-%H%M%S)"
mkdir -p "${run_dir}/stderr"
scratch_dir="$(mktemp -d "${TMPDIR:-/tmp}/hornix-svcomp25-mismatches.XXXXXX")"
trap 'rm -rf "${scratch_dir}"' EXIT

tasks="${run_dir}/selected.tsv"
awk -F '\t' -v limit="${limit}" '
    BEGIN { print "task_definition\tsource\texpected_verdict" }
    NR > 1 && $5 == "MISMATCH" {
        if (limit == 0 || count < limit) {
            print $1 "\t" $2 "\t" $3
            count += 1
        }
    }
' "${source_run}/results.tsv" > "${tasks}"

task_count="$(( $(wc -l < "${tasks}") - 1 ))"
if [[ "${task_count}" -eq 0 ]]; then
    echo "No MISMATCH rows in ${source_run}/results.tsv."
    exit 0
fi

echo "Re-running ${task_count} mismatches from ${source_run} with ${jobs} workers."
raw_results="${scratch_dir}/worker-results.tsv"
parallel --will-cite --jobs "${jobs}" --line-buffer --bar \
    --joblog "${run_dir}/joblog.tsv" --colsep '\t' \
    bash "${screen_script}" --worker-solve "${suite_dir}" "${hornix}" "${theory}" "${timeout_seconds}" "${run_dir}/stderr" {1} {2} {3} \
    :::: <(tail -n +2 "${tasks}") > "${raw_results}"

results="${run_dir}/results.tsv"
printf 'task_definition\tsource\texpected_verdict\thornix_result\tstatus\texit_code\tmessage\n' > "${results}"
cat "${raw_results}" >> "${results}"

printf 'status\tcount\n' > "${run_dir}/summary.tsv"
awk -F '\t' 'NR > 1 { count[$5] += 1 } END { for (status in count) print status "\t" count[status] }' "${results}" | LC_ALL=C sort >> "${run_dir}/summary.tsv"

echo "Complete. Results: ${run_dir}"
