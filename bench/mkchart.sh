#!/bin/sh
# Generate bench/results.svg, a horizontal bar chart of the parse_ms values in
# bench/RESULTS.md. No chart library: a hand-written SVG emitted by awk.
#
# Usage: sh bench/mkchart.sh
# Reads the markdown table rows of RESULTS.md (lines starting with "| " whose second
# column is numeric after stripping a leading "~") and writes bench/results.svg.
set -eu

dir=$(dirname "$0")
in="$dir/RESULTS.md"
out="$dir/results.svg"

awk -F '|' '
  BEGIN { n = 0; max = 0 }
  # collect table rows: label in $2, ms in $3 (strip spaces and a leading ~)
  /^\| / {
    label = $2; ms = $3
    gsub(/^[ \t]+|[ \t]+$/, "", label)
    gsub(/[ \t~]/, "", ms)
    if (ms ~ /^[0-9]+(\.[0-9]+)?$/ && label != "parser") {
      labels[n] = label; vals[n] = ms + 0; if (vals[n] > max) max = vals[n]; n++
    }
  }
  END {
    w = 720; rowh = 46; padL = 230; padR = 90; padT = 40; barMax = w - padL - padR
    h = padT + n * rowh + 20
    printf "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"%d\" height=\"%d\" font-family=\"sans-serif\">\n", w, h
    printf "<text x=\"20\" y=\"26\" font-size=\"18\" font-weight=\"bold\">grip: canada.json parse time (ms, lower is better)</text>\n"
    for (i = 0; i < n; i++) {
      y = padT + i * rowh
      bw = (max > 0) ? (vals[i] / max) * barMax : 0
      printf "<text x=\"20\" y=\"%d\" font-size=\"13\">%s</text>\n", y + 26, labels[i]
      printf "<rect x=\"%d\" y=\"%d\" width=\"%.1f\" height=\"24\" rx=\"3\" fill=\"#4c78a8\"/>\n", padL, y + 12, bw
      printf "<text x=\"%.1f\" y=\"%d\" font-size=\"13\">%.1f</text>\n", padL + bw + 8, y + 29, vals[i]
    }
    print "</svg>"
  }
' "$in" > "$out"

echo "wrote $out"
