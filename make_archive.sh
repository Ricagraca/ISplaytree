ARCHIVE=iris-time-proofs.tar.gz
rm -f $ARCHIVE
find theories/ -type f -name '*.v' -exec \
	tar -czvf $ARCHIVE README.md Makefile _CoqProject {} \+
