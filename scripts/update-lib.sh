git ls-files 'VCVio/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > VCVio.lean
git ls-files 'Examples/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Examples.lean
{ echo 'module'; echo ''; git ls-files 'ToMathlib/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/public import /'; } > ToMathlib.lean
