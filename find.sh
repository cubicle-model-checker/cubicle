find examples/ -iname "*.cub" -type f -print -exec ./cubicle.opt {} \;
find examples/ -iname "*.cub" -type f -exec grep -Hn "forall" {} \;
