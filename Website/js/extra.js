(function($) {
  "use strict"; // Start of use strict

  $('.js-scroll-trigger').click(function(){
    var divId = $(this).attr('href');
    $('html,body').animate({
      scrollTop: $(divId).offset().top - 54
    }, 500);
  });
  
})(jQuery); // End of use strict

// Enable source-code highlighting

var entityMap = {
  "&": "&amp;",
  "<": "&lt;",
  ">": "&gt;",
  '"': '&quot;',
  "'": '&#39;',
  "/": '&#x2F;'
};

function escapeHtml(string) {
  return String(string).replace(/[&<>"'\/]/g, function (s) {
    return entityMap[s];
  });
}

//document.addEventListener("DOMContentLoaded", init, false);

window.onload = function init() 
{
  var codeblock = document.querySelectorAll("pre code");
  
  if(codeblock.length) 
  {
    for(var i=0, len=codeblock.length; i<len; i++) 
    {
      var dom = codeblock[i];
      var html = dom.innerHTML;
      html = escapeHtml(html);
      dom.innerHTML = html;
    }
  }
}


hljs.initHighlightingOnLoad();
