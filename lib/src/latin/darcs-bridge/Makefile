DARCSPATH=/tmp/darcsGF
PATCHPATH=/tmp/git-patches

all: create-patches apply-patches update-darcs update-branch
create-patches:
	@echo "Create patches"
	rm -Rf /tmp/git-patches
	git format-patch -o $(PATCHPATH) darcs
apply-patches:
	@echo "Apply patches"
	sh apply-patches.sh $(shell pwd) $(DARCSPATH)
update-darcs:
	@echo "Update darcs"
update-branch:
	@echo "Update branch"
	git branch -f darcs
