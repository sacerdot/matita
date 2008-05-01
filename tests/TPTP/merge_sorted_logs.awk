BEGIN {LAST=""; ARGS="";}
 { 
   if (LAST == $1) {
       if ($3 == "OK" && length(ARGS) < length($0)) {
          ARGS=$0;
       }  
   } else {
       print ARGS;
       LAST=$1;
       ARGS=$0;
  }
   
 }
END{ print ARGS; }
