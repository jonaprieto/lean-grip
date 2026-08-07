# grip core benchmark

The core benchmark measures the byte parser through the S-expression, lambda, HTTP, TOML, and
flow-style YAML examples. JSON validation and DOM measurements live in
[`lean-grip-json`](https://github.com/jonaprieto/lean-grip-json), where the JSON corpus and
cross-language harnesses stay with the parser they measure.

Run `lake exe bench` to collect the current machine's timings. Counts are the correctness gate;
timings are recorded for comparison and are not treated as a CI threshold.
