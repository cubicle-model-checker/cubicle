;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Cubicle major mode for emacs                                               ;;
;;                                                                            ;;
;; Author: Alain Mebsout                                                      ;;
;;                                                                            ;;
;; Usage:                                                                     ;;
;;   Copy this file to a location of your load path (e.g. ~/.emacs.d) and add ;;
;;   the following to your .emacs (or .emacs.d/init.el):                      ;;
;;                                                                            ;;
;; ;-----------------                                                         ;;
;; ; mode Cubicle                                                             ;;
;; ;-----------------                                                         ;;
;; (setq auto-mode-alist                                                      ;;
;;       (cons '("\\.cub$" . cubicle-mode) auto-mode-alist))                  ;;
;; (autoload 'cubicle-mode "cubicle-mode" "Major mode for Cubicle." t)        ;;
;;                                                                            ;;
;; To add colors to the compilation buffer, also add this:                    ;;
;; (require 'ansi-color)                                                      ;;
;; (defun colorize-compilation-buffer ()                                      ;;
;;   (toggle-read-only)                                                       ;;
;;   (ansi-color-apply-on-region (point-min) (point-max))                     ;;
;;   (toggle-read-only))                                                      ;;
;; (add-hook 'compilation-filter-hook 'colorize-compilation-buffer)           ;;
;;                                                                            ;;
;;                                                                            ;;
;; You can also use Cubicle in org-mode through babel by adding the following ;;
;; to your .emacs:                                                            ;;
;;                                                                            ;;
;; (defun org-babel-execute:cubicle (body params)                             ;;
;;   "Execute a block of Cubicle code with org-babel."                        ;;
;;   (message "executing Cubicle source code block")                          ;;
;;   (let ((brab (cdr (assoc :brab (org-babel-process-params params)))))      ;;
;;     (if brab                                                               ;;
;;         (org-babel-eval (format "cubicle -brab %S" brab) body)             ;;
;;         (org-babel-eval "cubicle" body)                                    ;;
;;       )))                                                                  ;;
;;                                                                            ;;
;; In this case you can define Cubicle source blocks and evaluate them with   ;;
;; #+begin_src cubicle :brab 2                                                ;;
;; #+end_src                                                                  ;;
;; where :brab is an optional argument that will be passed on to cubicle when ;;
;; executed                                                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar cubicle-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\( ". 1" st)
    (modify-syntax-entry ?\) ". 4" st)
    (modify-syntax-entry ?* ". 23" st)
    (modify-syntax-entry ?_ "w" st)
    st)
  "Syntax table for `cubicle-mode'.")

(defvar cubicle-font-lock-keywords
  '(
    ("(\\*\\([^*]\\|\\*[^)]\\)*\\*)" . font-lock-comment-face)
    ; transitions need not have a return type
    ("\\(transition\\)\\s-+\\(\\sw+\\)" (1 font-lock-keyword-face) (2 font-lock-function-name-face))
    ("\\(type\\)\\s-+\\(\\sw+\\)" (1 font-lock-keyword-face) (2 font-lock-type-face))
    ("\\(var\\)\\s-+\\sw+\\s-+:\\s-+\\(\\sw+\\)" (1 font-lock-keyword-face) (2 font-lock-type-face))
    ("\\(array\\)\\s-+\\sw+\\[\\(\\sw+\\s-*,?\\s-*\\)*\\]\\s-*:\\s-*\\(\\sw+\\)"
     (1 font-lock-keyword-face) (2 font-lock-type-face) (3 font-lock-type-face))
    ("\\b\\(bool\\)\\b" (1 font-lock-type-face))
    ("\\b\\(int\\)\\b" (1 font-lock-type-face))
    ("\\b\\(real\\)\\b" (1 font-lock-type-face))
    ("\\b\\(proc\\)\\b" (1 font-lock-type-face))
    ("\\b\\(init\\)\\b" (1 font-lock-builtin-face))
    ("\\b\\(unsafe\\)\\b" (1 font-lock-builtin-face))
    ("\\b\\(invariant\\)\\b" (1 font-lock-builtin-face))
    ("\\b\\(array\\)\\b" (1 font-lock-keyword-face))
    ("\\b\\(var\\)\\b" (1 font-lock-keyword-face))
    ("\\b\\(const\\)\\b" (1 font-lock-keyword-face))
    ;; ("\\(requires\\)" (1 font-lock-variable-name-face))
    ("\\b\\(requires\\)\\b" (1 font-lock-builtin-face))
    ("\\b\\(forall_other\\)\\b" (1 font-lock-builtin-face))
    ("\\b\\(case\\)\\b" (1 font-lock-keyword-face))
    ("\\(&&\\)" (1 font-lock-variable-name-face))
    ("\\(||\\)" (1 font-lock-variable-name-face))
    ;("\\(|\\)" (1 font-lock-keyword-face))
    ("\\<[a-z][a-zA-Z0-9_]*" . font-lock-constant-face)
    ("\\#[0-9]*" . font-lock-constant-face)

    "Keyword highlighting specification for `cubicle-mode'."))

(require 'compile)
(define-derived-mode cubicle-mode fundamental-mode "Cubicle"
  "A major mode for editing Cubicle files."
  :syntax-table cubicle-mode-syntax-table
  (set (make-local-variable 'comment-start) "(*")  
  (set (make-local-variable 'comment-end) "*)")
  (when (buffer-file-name)
    (set (make-local-variable 'compile-command)
         (format "cubicle %s" (file-name-nondirectory buffer-file-name))))
  (set (make-local-variable 'font-lock-defaults)'(cubicle-font-lock-keywords))
  )
(provide 'cubicle-mode)