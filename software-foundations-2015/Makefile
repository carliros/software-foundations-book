BUILD = build
BOOKNAME = Software-Foundation
TITLE = title.txt
METADATA = metadata.xml

CHAPTERS = 01-Preface.md 02-Basics.md 03-Induction.md 04-Lists.md
#05-Poly.md 06-MoreCoq.md 07-Logic.md 08-Prop.md 09-MoreLogic.md 10-ProofObjects.md 11-MoreInd.md 12-SfLib.md 13-Rel.md 14-Imp.md 15-ImpParser.md 16-ImpCEvalFun.md 17-Extraction.md 18-Equiv.md 19-Hoare.md 20-Hoare2.md 21-HoareAsLogic.md 22-Smallstep.md 23-Auto.md 24-Types.md 25-Stlc.md 26-StlcProp.md 27-MoreStlc.md 28-Sub.md 29-Typechecking.md 30-Records.md 31-References.md 32-RecordSub.md 33-Norm.md 34-LibTactics.md 35-UseTactics.md 36-UseAuto.md 37-PE.md 38-Postscript.md

TOC = --toc --toc-depth=2
COVER_IMAGE = img/cover.png
LATEX_CLASS = report
KINDLEC = ~/KindleGen/kindlegen

all: book

book: epub html pdf

clean:
	rm -r $(BUILD)

epub: $(BUILD)/epub/$(BOOKNAME).epub

html: $(BUILD)/html/$(BOOKNAME).html

pdf: $(BUILD)/pdf/$(BOOKNAME).pdf

mobi: epub $(BOOKNAME).mobi

$(BUILD)/epub/$(BOOKNAME).epub: $(TITLE) $(addprefix en/, $(CHAPTERS))
	mkdir -p $(BUILD)/epub
	pandoc $(TOC) -S --epub-metadata=$(METADATA) --epub-cover-image=$(COVER_IMAGE) -o $@ $^

$(BUILD)/html/$(BOOKNAME).html: $(addprefix en/, $(CHAPTERS))
	mkdir -p $(BUILD)/html
	pandoc $(TOC) --standalone --to=html5 -o $@ $^

$(BUILD)/pdf/$(BOOKNAME).pdf: $(TITLE) $(addprefix en/, $(CHAPTERS))
	mkdir -p $(BUILD)/pdf
	pandoc $(TOC) --latex-engine=xelatex -V documentclass=$(LATEX_CLASS) -o $@ $^

$(BOOKNAME).mobi: $(BUILD)/epub/$(BOOKNAME).epub
	mkdir -p $(BUILD)/mobi
	$(KINDLEC) -o $@ $^
#	mv $(BUILD)/epub/$(BOOKNAME).mobi $(BUILD)/mobi/


.PHONY: all book clean epub html pdf


