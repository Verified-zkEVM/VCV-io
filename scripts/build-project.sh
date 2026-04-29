# Building the examples already builds this
# echo "# Building VCVio library"
# lake build VCVio

echo "# Building Project"
lake build Examples

echo "\n# Linting Files"
scripts/lint-style.sh && echo "All files okay"
