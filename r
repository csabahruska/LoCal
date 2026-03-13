set -x -e

#idris2 -p contrib --cg chez -Xcase-tree-opt $@
idris2 -p contrib --cg node -Xcase-tree-opt $@
#idris2 -p contrib --cg chez $@
#idris2 -p contrib --cg refc $@

# chez scheme is slow for some reason
