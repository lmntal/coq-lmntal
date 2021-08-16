#!/bin/bash

for i in *.v; do
  ./make_graph.sh $i
done
