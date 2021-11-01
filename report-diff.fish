function report-diff --argument ignoreTok
    set -l errors 0
    set -l diffs 0
    for f in (git diff --name-only | rg "\\.ast")
        if test ! -f $f
            continue
        end
        echo "==" $f "=="
        if rg "^(Error:|Fatal error:|Segmentation fault)" $f > /dev/null && not rg "^(Error:|Fatal error:|Segmentation fault)" (git show HEAD:$f | psub) > /dev/null
            # Parse error, show the error
            cat $f
            set errors (math $errors + 1)
        else
            # Parsed correctly, but gave the wrong AST, show the diff
            # icdiff (git show HEAD:$f | psub) $f
            if test -n "$ignoreTok"
                icdiff\
                    (git show HEAD:$f | sed -E 's#(\([-a-zA-Z0-9/._]+\[[0-9]+,)[0-9]+\+[0-9]+(\]\.\.\[[0-9]+,)[0-9]+\+[0-9]+(\]\))#\1\2\3#g' | psub)\
                    (cat $f | sed -E 's#(\([-a-zA-Z0-9/._]+\[[0-9]+,)[0-9]+\+[0-9]+(\]\.\.\[[0-9]+,)[0-9]+\+[0-9]+(\]\))#\1\2\3#g' | psub)
            else
                git --no-pager diff --color=always $f | tail --lines=+5
            end
            set diffs (math $diffs + 1)
        end
        echo
        echo
    end

    echo -e "Errors:\t"$errors
    echo -e "Diffs:\t"$diffs
    echo -e "Total:\t"(math $errors + $diffs)
end

function canon-diff --argument file nonSide
    if test -n "$nonSide"
        set nonSide "-C5"
    else
        set nonSide "-y --left-column"
    end
    echo $file | entr -rcs "icdiff (~/Projects/static-resolvable/ocaml/boot/ocamlrun ~/Projects/static-resolvable/ocaml/boot/ocamlc -nostdlib -nopervasives -stop-after parsing -dparsetree $file 2>&1 | psub) (~/Projects/static-resolvable/ocaml/boot/ocamlrun ~/Projects/static-resolvable/ocaml/ocamlc -nostdlib -nopervasives -stop-after parsing -dparsetree $file 2>&1 | psub)"
end
