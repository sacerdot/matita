function filter(ptr) {
  var query = document.getElementById('f.'+ptr).value;
  var cl = document.getElementsByName(ptr);
  for (i=0;i < cl.length; i++) {
    if (cl[i].getAttribute('key').search(query) >= 0) {
      cl[i].classList.remove('hidden')
    } else {
      cl[i].classList.add('hidden')
    }
  }
}
