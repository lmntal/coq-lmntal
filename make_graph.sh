#!/bin/bash -x

cd $(dirname $0)

file=$(echo "$(basename "$1")" | sed "s/\..*$//")

make

coqtop <<EOS
Add LoadPath "." as LMNTAL.
From LMNTAL Require ${file}.
Require dpdgraph.dpdgraph.
Print FileDependGraph ${file}.
EOS

dpd2dot graph.dpd

dot -Tpdf graph.dot > ${file}.pdf
dot -Tpng graph.dot > ${file}.png
dot -Tsvg graph.dot > ${file}.svg
