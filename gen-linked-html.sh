#!/bin/bash
while getopts "o:" opt; do
    case "${opt}" in
        o)
            OPTION=${OPTARG}
    esac
done

src_dir=${@:$OPTIND:1}
out_dir=${@:$OPTIND+1:1}
SESSION=${@:$OPTIND+2:1}
ROOT="$src_dir/ROOT"
mkdir "$out_dir/html"

# Use Isabelle to build HTML 
isabelle env \
	ISABELLE_BROWSER_INFO="$out_dir/html"\
	isabelle build -o $OPTION -d $src_dir -c -o browser_info -v $SESSION

# Link HTML 
rm -rf "$out_dir/html_linked" 
cat scripts/links.css >> "$out_dir/html_linked/isabelle.css" 
python parsing.py $SESSION
python linking.py $SESSION . . 

