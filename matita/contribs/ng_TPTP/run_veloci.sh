for X in `cat Veloci`;
do
echo $X;
touch $X;
../../matitac.opt $X 2> /dev/null
done

