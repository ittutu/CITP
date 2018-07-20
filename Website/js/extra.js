(function($) {
  "use strict"; // Start of use strict

  $('.js-scroll-trigger').click(function(){
    var divId = $(this).attr('href');
    $('html,body').animate({
      scrollTop: $(divId).offset().top - 54
    }, 500);
  });

  // Enable source-code highlighting
  $(document).ready(function() {
    $('pre code').each(function(i, block) {
      hljs.highlightBlock(block);
    });
  });
  
})(jQuery); // End of use strict
