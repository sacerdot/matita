 {
	result=tolower($3);
	if( $1 ~ ".opt$" )
		compilation="opt"
	else
		compilation="byte"
	test=$2	
	time=$4
	timeuser=$5
	mark=$7
	if ( $8 ~ "^gc-off$") 
		options="'gc-off'";
	if ( $8 ~ "^gc-on$") 
		options="'gc-on'"
		
	printf "INSERT bench (result, compilation, test, time, timeuser, mark, options) VALUES ('%s', '%s', '%s', '%s', '%s', '%s', %s);\n", result, compilation, test, time, timeuser, mark, options;
	}
