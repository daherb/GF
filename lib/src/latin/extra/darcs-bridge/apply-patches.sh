OLDPWD=$1
DARCSPATH=$2
cd $DARCSPATH
echo "In $DARCSPATH"
for p in /tmp/git-patches/*.patch
do
  echo "Merging $p"
  patch -p1 < $p
  perl $OLDPWD/set-patch-name.pl $p $DARCSPATH
done
