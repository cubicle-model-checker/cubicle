
var input = document.getElementById("input");
var output = document.getElementById("output");
var for_filename = document.getElementById("filename");

// Check for the various File API support.
if (window.File && window.FileReader && window.FileList && window.Blob) {
  // Great success! All the File APIs are supported.
} else {
    var msg = "";
    if (window.File) { msg += "window.File is supported<br/>"; }
    if (window.FileReader) { msg += "window.FileReader is supported<br/>"; }
    if (window.FileList) { msg += "window.FileList is supported<br/>"; }
    if (window.Blob) { msg += "window.Blob is supported<br/>"; }
    for_filename.innerHTML ='Warning: the File API is not fully supported in this browser.<br/>' + msg;
}

function loadFiles(files){

    // Loop through the FileList and render image files as thumbnails.
    for (var i = 0, f; f = files[i]; i++) {
        var filename = "";
        if ('name' in f) { filename = f.name; }
        else { filename = f.fileName; }
        for_filename.innerHTML = "";
        var reader = new FileReader();
        function receivedText(e) {
            input.value = ""+reader.result;
            output.innerHTML = "";
            for_filename.innerHTML = filename;
        };

      // Closure to capture the file information.
      reader.onloadend = receivedText;

      // Read in the image file as a data URL.
      reader.readAsText(f) ;
    }
}

function handleFileSelect(evt) {
    var files = evt.target.files; // FileList object
    loadFiles(files);
  }


document.getElementById('files').addEventListener('change', handleFileSelect, false);



  function handleFileSelect2(evt) {
    evt.stopPropagation();
    evt.preventDefault();

    var files = evt.dataTransfer.files; // FileList object.
    loadFiles(files);
  }

  function handleDragOver(evt) {
    evt.stopPropagation();
    evt.preventDefault();
    evt.dataTransfer.dropEffect = 'copy'; // Explicitly show this is a copy.
  }

  // Setup the dnd listeners.
  var dropZone = document.getElementById('drop_zone');
  dropZone.addEventListener('dragover', handleDragOver, false);
  dropZone.addEventListener('drop', handleFileSelect2, false);
