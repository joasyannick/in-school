all: lib

COQC=coqc
COQFLAGS=-R theories LSMTS
COQDOC=coqdoc
DOCDIR=doc/lib
DOCFLAGS=--utf8 --html -d $(DOCDIR)

LIBDIR=theories
LIBDIRCLS=$(LIBDIR)/Classes
LIBDIRXMPL=$(LIBDIR)/Examples
LIBDIRSETS=$(LIBDIR)/Sets
LIBDIRTS=$(LIBDIR)/TransitionSystems
LIBDIRCCT=$(LIBDIR)/Contracts


clean: clean-lib clean-doc

clean-lib:
	find $(LIBDIR) \( -name '*.vo' -or -name '*.glob' \) -delete

clean-doc:
	find $(DOCDIR) \( -name '*.css' -or -name '*.html' \) -delete

lib: ModalTransitionSystem.vo

ModalTransitionSystem.vo: NaiveSet.vo PartialOp.vo Transition.vo Order.vo Contract.vo LabelSet.vo LabelOp.vo TransitionSystem.vo $(LIBDIRTS)/ModalTransitionSystem.v
	$(COQC) $(LIBDIRTS)/ModalTransitionSystem.v $(COQFLAGS)
	$(COQDOC) $(LIBDIRTS)/ModalTransitionSystem.v $(DOCFLAGS)

LabelOp.vo: DecidableRelation.vo PartialOp.vo Order.vo LabelSet.vo $(LIBDIRTS)/LabelOp.v
	$(COQC) $(LIBDIRTS)/LabelOp.v $(COQFLAGS)
	$(COQDOC) $(LIBDIRTS)/LabelOp.v $(DOCFLAGS)

LabelSet.vo: NaiveSet.vo DecidableRelation.vo Order.vo DecidableOrder.vo $(LIBDIRTS)/LabelSet.v
	$(COQC) $(LIBDIRTS)/LabelSet.v $(COQFLAGS)
	$(COQDOC) $(LIBDIRTS)/LabelSet.v $(DOCFLAGS)

Contract.vo : NaiveSet.vo PartialOp.vo Order.vo $(LIBDIRCCT)/Contract.v
	$(COQC) $(LIBDIRCCT)/Contract.v $(COQFLAGS)
	$(COQDOC) $(LIBDIRCCT)/Contract.v $(DOCFLAGS)

DecidableOrder.vo: DecidableRelation.vo Order.vo $(LIBDIRCLS)/DecidableOrder.v
	$(COQC) $(LIBDIRCLS)/DecidableOrder.v $(COQFLAGS)
	$(COQDOC) $(LIBDIRCLS)/DecidableOrder.v $(DOCFLAGS)

Order.vo: NaiveSet.vo $(LIBDIRCLS)/Order.v
	$(COQC) $(LIBDIRCLS)/Order.v $(COQFLAGS)
	$(COQDOC) $(LIBDIRCLS)/Order.v $(DOCFLAGS)

TransitionSystem.vo: NaiveSet.vo Transition.vo $(LIBDIRTS)/TransitionSystem.v
	$(COQC) $(LIBDIRTS)/TransitionSystem.v $(COQFLAGS)
	$(COQDOC) $(LIBDIRTS)/TransitionSystem.v $(DOCFLAGS)

Transition.vo: $(LIBDIRTS)/Transition.v
	$(COQC) $(LIBDIRTS)/Transition.v $(COQFLAGS)
	$(COQDOC) $(LIBDIRTS)/Transition.v $(DOCFLAGS)

PartialOp.vo: $(LIBDIRCLS)/PartialOp.v
	$(COQC) $(LIBDIRCLS)/PartialOp.v $(COQFLAGS)
	$(COQDOC) $(LIBDIRCLS)/PartialOp.v $(DOCFLAGS)

DecidableRelation.vo : $(LIBDIRCLS)/DecidableRelation.v
	$(COQC) $(LIBDIRCLS)/DecidableRelation.v $(COQFLAGS)
	$(COQDOC) $(LIBDIRCLS)/DecidableRelation.v $(DOCFLAGS)

NaiveSet.vo: $(LIBDIRSETS)/NaiveSet.v
	$(COQC) $(LIBDIRSETS)/NaiveSet.v $(COQFLAGS)
	$(COQDOC) $(LIBDIRSETS)/NaiveSet.v $(DOCFLAGS)

internship:
	cd doc/internship;\
	pdflatex memoir.tex;\
	biber memoir;\
	pdflatex memoir.tex;\
	cd ../..

clean-internship:
	find doc/internship \(\
		-name '*.aux'\
		-or -name '*.toc'\
		-or -name '*.xml'\
		-or -name '*.out'\
		-or -name '*.bcf'\
		-or -name '*.blg'\
		-or -name '*.bbl' \)\
			-delete
