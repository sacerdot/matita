<?php
 require($argv[1]);
 $rc = query($argv[2]);
 $a = array_values($rc[0]); 
 print($a[0]);
?>
