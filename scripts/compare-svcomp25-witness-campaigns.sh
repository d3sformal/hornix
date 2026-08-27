#!/usr/bin/env bash
# Compare per-task outcomes from two svcomp25-witness-campaign runs.

set -euo pipefail

usage() {
    cat <<'EOF'
Usage: scripts/compare-svcomp25-witness-campaigns.sh Z3_RUN ELDARICA_RUN [OUTPUT_DIR]

Create comparison.tsv and summary.tsv from the results.tsv files of two
svcomp25-witness-campaign runs.  The input runs should use the same selected
task set and timeout.  Per-task Hornix wall-clock milliseconds are compared;
the total campaign wall time depends on --jobs and is intentionally not used.
EOF
}

[[ $# -ge 2 && $# -le 3 ]] || { usage >&2; exit 2; }
z3_dir="$(cd "$1" && pwd)"
eldarica_dir="$(cd "$2" && pwd)"
project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
output_dir="${3:-${project_dir}/results/svcomp25-witness-comparison-$(date +%Y%m%d-%H%M%S)}"
[[ -f "${z3_dir}/results.tsv" && -f "${eldarica_dir}/results.tsv" ]] || {
    echo "Both arguments must be campaign result directories." >&2
    exit 2
}
mkdir -p "${output_dir}"

comparison="${output_dir}/comparison.tsv"
printf 'source\tz3_result\tz3_status\tz3_hornix_ms\teldarica_result\teldarica_status\teldarica_hornix_ms\tclassification\n' > "${comparison}"
awk -F '\t' 'BEGIN { OFS = "\t" }
    NR == FNR {
        if (FNR > 1) {
            z_result[$3] = $5; z_status[$3] = $11; z_time[$3] = $7; sources[$3] = 1
        }
        next
    }
    FNR > 1 {
        e_result[$3] = $5; e_status[$3] = $11; e_time[$3] = $7; sources[$3] = 1
    }
    END {
        for (source in sources) {
            if (!(source in z_result) || !(source in e_result)) classification = "MISSING_FROM_ONE_RUN"
            else if (z_status[source] == "VALIDATED" && e_status[source] == "VALIDATED") classification = "BOTH_VALIDATED"
            else if (z_status[source] == "VALIDATED") classification = "Z3_ONLY_VALIDATED"
            else if (e_status[source] == "VALIDATED") classification = "ELDARICA_ONLY_VALIDATED"
            else classification = "NEITHER_VALIDATED"
            print source, z_result[source], z_status[source], z_time[source], \
                  e_result[source], e_status[source], e_time[source], classification
        }
    }
' "${z3_dir}/results.tsv" "${eldarica_dir}/results.tsv" | LC_ALL=C sort >> "${comparison}"

printf 'classification\tcount\n' > "${output_dir}/summary.tsv"
awk -F '\t' 'NR > 1 { count[$8] += 1 } END { for (key in count) print key "\t" count[key] }' "${comparison}" | LC_ALL=C sort >> "${output_dir}/summary.tsv"
printf 'z3_run\t%s\neldarica_run\t%s\n' "${z3_dir}" "${eldarica_dir}" > "${output_dir}/configuration.tsv"
echo "Comparison: ${output_dir}"
