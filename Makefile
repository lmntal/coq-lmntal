all:
	coqc Util.v -Q . LMNTAL
	coqc LMNtalSyntax.v -Q . LMNTAL
	# coqc LMNtalShapeType.v -Q . LMNTAL
	coqc LMNtalGraph.v -Q . LMNTAL
	coqc Properties.v -Q . LMNTAL

clean:
	@rm -rf .*.aux *.vo *.glob
