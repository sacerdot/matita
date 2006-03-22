<?php require("common.php"); 

  $query = stripslashes($_GET['query']);

  $nqs = explode('###',$query);

  $qs = array();
  foreach($nqs as $v){
    $x = explode("@@@",$v);
    if ($x[1] == NULL) {
      $qs["Unnamed"] = $x[0];
    } else {
      $qs[$x[0]] = $x[1];
    }
  }

?>
<html>
  <head>
  <link type="text/css" rel="stylesheet" href="style.css"/>
  </head>
  <body>
    <h1>QUERY results</h1>
<? foreach( $qs as $name => $q) { $i=0;?>
    <h2><? echo $name; ?></h2>
    <p>
    <tt><? echo $q; ?></tt>
    </p>
    <table border=1>
    <?  query($q,"printer"); ?>
    </table>
<? } ?>
    <p><a href="bench.php">BACK to the query page</a></p>
  </body>
</html>
