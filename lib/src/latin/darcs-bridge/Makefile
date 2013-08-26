all: create-patches update-branch apply-patches update-darcs
create-patches
	echo "Create patches"
	git format-patch -o /tmp/git-patches darcs
apply-patches
	echo "Apply patches"
update-darcs
	echo "Update darcs"
update-branch
	echo "Update branch"