all:
	coqc LMNtalSyntax.v -Q . LMNTAL
	coqc LMNtalShapeType.v -Q . LMNTAL

clean:
	@rm -rf .*.aux *.vo *.glob
