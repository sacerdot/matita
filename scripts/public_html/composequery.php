<?php require("common.php"); 
  
  $c = array("mark", "options", "test", "result", "compilation");

  function clause_for($c) {
    $fst = true;
    $rc = "";
    foreach($c as $fake => $x) {
      $v = $_GET[$x];
      if($v != "--") {
        if($fst == false) {
          $rc = $rc . " and "; 
        } else {
          $rc = $rc . " ";
        }
        $fst = false;
        $rc = $rc . $x . " = '" . $v . "'";
      }
    }
    return $rc;
  }
  
  $gb = $_GET['groupby'];
  $limit = $_GET['limit'];
  if($gb != "--")
    $what = "mark, SEC_TO_TIME(SUM(TIME_TO_SEC(time))) as sum_time, SEC_TO_TIME(SUM(TIME_TO_SEC(timeuser))) as sum_timeuser";
  else
    $what = "mark, time, timeuser, compilation, test, result, options";
  $clause = clause_for($c);
  if($clause != "")
    $query = "select $what from bench where " .  clause_for($c);
  else
    $query = "select $what from bench ";
  if( $gb != "--"){
    $query = $query. "group by $gb";
  }

  if($limit != "--") {
    $query = $query. " LIMIT 0,$limit";
  }

   $query = $query. ";"; 

   header("Location: showquery.php?query=".urlencode("Custom:@@@" . $query));
   exit;
?>
