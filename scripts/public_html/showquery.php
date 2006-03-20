<?php require("common.php"); 

  $query = stripslashes($_GET['query']);

  $nqs = explode('###',$query);

  $qs = array();
  foreach($nqs as $v){
    $x = explode("@@@",$v);
    $qs[$x[0]] = $x[1];
  }

function prettify($s,$name) {
  if (preg_match("/^[0-9]{12}$/",$s)) {
    $year = substr($s,0,4);
    $month = substr($s,4,2);
    $day = substr($s,6,2);
    $hour = substr($s,8,2);
    $minute = substr($s,10,2);
    return $day . "/" . $month . "/" . $year . " " . $hour . ":" . $minute;
  } else if ($name == "sum_time" || $name == "sum_timeuser" || $name == "time" || $name == "time_user" || $name == "timeuser"){
    $min = floor($s / 6000);
    $sec = floor(($s - $min * 6000) / 100);
    $cents = $s % 100;
    return $min . "m" . $sec . "." . $cents . "s";
  } else
    return $s;
}
  
function printer($q){
  global $i;
  echo "<tr>";
  if ( $i == 0) {
      foreach( $q as $name => $txt) {
          echo "<th>$name</th>";
      }
  }
  echo "</tr>\n";
  if ( $i%2 == 0)
     echo "<tr class=\"even\">";      
  else
     echo "<tr class=\"odd\">";
  foreach( $q as $name => $txt) {
     echo "<td>" . prettify($txt,$name) . "</td>";
  }
  echo "</tr>\n";      
  $i++;
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
    <tt><? print $q; ?></tt>
    </p>
    <table border=1>
    <?  query($q,"printer"); ?>
    </table>
<? } ?>
    <p><a href="bench.php">BACK to the query page</a></p>
  </body>
</html>
