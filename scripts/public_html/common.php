<?php

function array_to_combo($a) {
  foreach($a as $k => $v){
    echo "<option value=\"{$v}\">{$v}</option>";
  }
}

function query($q,$f) {
  $db = mysql_pconnect("localhost","helm");
  mysql_select_db("matita");
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
