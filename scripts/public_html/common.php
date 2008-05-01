<?php

$i = 0;
  
function array_to_combo($a) {
  foreach($a as $k => $v){
    echo "<option value=\"{$v}\">{$v}</option>";
  }
}

function prettify($s,$name) {
  if (preg_match("/^[0-9]{12}$/",$s)) {
    $year = substr($s,0,4);
    $month = substr($s,4,2);
    $day = substr($s,6,2);
    $hour = substr($s,8,2);
    $minute = substr($s,10,2);
    return $day . "/" . $month . "/" . $year . " " . $hour . ":" . $minute;
  } else if (preg_match("/time/",$name)){
    $min = floor($s / 6000);
    $sec = floor(($s - $min * 6000) / 100);
    $cents = $s % 100;
    return $min . "m" . $sec . "." . $cents . "s";
  } else
    return rtrim($s);
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


function query($q,$f) {
  $db = mysql_pconnect("localhost","helm");
  mysql_select_db("matita");
  $q = ltrim(rtrim(preg_replace("/\n/"," ",$q)));
  if (!preg_match("/^(select|describe)[^\n;]*;?$/i",$q)) {
    die("Query not allowed!<pre>" . $q . "</pre>");
    return;
  }
  $rc = mysql_query($q,$db);
  if(!$rc) {
    die("Query failed: " . mysql_error());
  }
  while( $row = mysql_fetch_array($rc, MYSQL_ASSOC)){
    $f($row);
  }
  mysql_free_result($rc);
  mysql_close($db);
}

function time_2_cents($t) {
  $matches = array();
  $rex = "/^(\d+)m(\d\d?)\.(\d{2})s$/";
  $m = preg_match($rex,$t,$matches);
  if ( $m == 0 ) exit(1);
  $t_minutes = $matches[1];
  $t_secs = $matches[2];
  $t_cents = $matches[3];
  return ((int) $t_cents) + ((int) $t_secs) * 100 + ((int)$t_minutes) * 6000 ;
}

?>
