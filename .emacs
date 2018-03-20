(require 'tramp)
(setq tramp-default-method "ssh")
(setq password-cache-expiry nil)
(setq shell-file-name "zsh")
(setq shell-command-switch "-ic")

(require 'package) ;; You might already have this line
(add-to-list 'package-archives
             '("melpa" . "http://melpa.org/packages/") t)
(add-to-list 'package-archives
             '("marmalade" . "http://marmalade-repo.org/packages/"))
;; (when (< emacs-major-version 24)
;;   ;; For important compatibility libraries like cl-lib
;;   (add-to-list 'package-archives '("gnu" . "http://elpa.gnu.org/packages/")))
(package-initialize) ;; You might already have this line

(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(ac-use-fuzzy nil)
 '(ansi-color-names-vector
   ["#2e3436" "#a40000" "#4e9a06" "#c4a000" "#204a87" "#5c3566" "#729fcf" "#eeeeec"])
 '(browse-url-netscape-arguments nil)
 '(browse-url-netscape-program "firefox")
 '(browse-url-netscape-startup-arguments (quote ("-remote")))
 '(browse-url-netscape-version 4)
 '(column-number-mode t)
 '(compilation-context-lines 2)
 '(compilation-error-screen-columns nil)
 '(compilation-scroll-output t)
 '(compilation-search-path (quote (nil "src")))
 '(custom-enabled-themes (quote (tango-dark)))
 '(delete-selection-mode nil)
 '(electric-indent-mode nil)
 '(inhibit-startup-screen t)
 '(line-move-visual t)
 '(next-error-highlight t)
 '(next-error-highlight-no-select t)
 '(next-line-add-newlines nil)
 '(nil nil t)
 '(require-final-newline t)
 '(safe-local-variable-values (quote ((TeX-Master . "these") (TeX-Master . t))))
 '(scroll-bar-mode (quote right))
 '(show-paren-mode t)
 '(show-trailing-whitespace t)
 '(tool-bar-mode nil)
 '(tuareg-function-indent 2)
 '(tuareg-match-clause-indent 0)
 '(tuareg-type-indent 2)
 '(tuareg-use-abbrev-mode t)
 '(tuareg-with-indent 2)
 '(use-file-dialog nil)
 '(user-mail-address "roux@lri.fr")
 '(visible-bell t)
 '(vm-delete-after-saving t))

(add-hook 'before-save-hook 'delete-trailing-whitespace)


;; Preset width nlinum
(add-hook 'nlinum-mode-hook
          (lambda ()
            (setq nlinum--width
                  (length (number-to-string
                           (count-lines (point-min) (point-max)))))))

;; (autoload 'iso-latin-1-mode "iso-latin-1" "Mode for editing accented text" t) (add-hook 'mail-mode-hook '(lambda () (iso-latin-1-mode 1)))
;; (set-language-environment 'latin-1)
;; (set-input-mode (car (current-input-mode)) (nth 1 (current-input-mode)) 0)
;; (define-key function-key-map [dead-circumflex] 'compose-circumflex-map)

(require 'iso-transl)

(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(default ((t (:family "DejaVu Sans Mono" :foundry "unknown" :slant normal :weight normal :height 113 :width normal)))))

(setq frame-title-format '(buffer-file-name "%b (%f)" "%b"))

(setq load-path (cons "~/.emacs.d/mymodes/" load-path))
;; Load merlin-mode
;; (require 'merlin)

;; SMT2 mode
(setq auto-mode-alist (cons '("\\.smt2$" . smtlib-mode) auto-mode-alist))
(autoload 'smtlib-mode "smtlib" "Major mode for SMTLIB" t)

(setq smtlib-solver-cmd "z3")

(global-nlinum-mode 1)

;; Demande y/n au lieu de yes/no (plus rapide)
(fset 'yes-or-no-p 'y-or-n-p)

                                        ;(add-to-list 'load-path "/home/mattiasroux/.emacs.d/")
                                        ;(require 'auto-complete-config)
                                        ;(add-to-list 'ac-dictionary-directories "/home/mattiasroux/.emacs.d//ac-dict")
                                        ;(ac-config-default)

(global-font-lock-mode 1)

(setq vm-url-browser 'vm-mouse-send-url-to-netscape)

                                        ; Revert buffer automatique
(global-auto-revert-mode 1)
(turn-on-auto-fill)

                                        ; (global-set-key [(meta c)] 'goto-char)

;;; no sendmail agent on the local machine
(setq send-mail-function                'smtpmail-send-it
      message-send-mail-function        'smtpmail-send-it
      smtpmail-smtp-service             "smtp"
      sendmail-program                  "MAIL_NOT_SENT"
      smtpmail-debug-info               nil
      smtpmail-smtp-server              "smtpext.lri.fr")
(load-library "smtpmail")

(if (>= emacs-major-version 21) (tool-bar-mode 0))

;; Helper for compilation. Close the compilation window if
;; there was no error at all.
;; (defun compilation-exit-autoclose (status code msg)
;;   ;; If M-x compile exists with a 0
;;   (when (and (eq status 'exit) (zerop code))
;;     ;; then bury the *compilation* buffer, so that C-x b doesn't go there
;;     (bury-buffer)
;;     ;; and delete the *compilation* window
;;     (delete-window (get-buffer-window (get-buffer "*compilation*"))))
;;   ;; Always return the anticipated result of compilation-exit-message-function
;;   (cons msg code))
;; ;; Specify my function (maybe I should have done a lambda function)
;; (setq compilation-exit-message-function 'compilation-exit-autoclose)

;;-----------------
;; mode LaTeX
;;-----------------

;; invoke the AUCTeX package (LaTeX support)
(require 'tex-site)

;; break lines at space when they are too long
(add-hook 'text-mode-hook 'turn-on-auto-fill)

;; highlight the region whenever it is active
(transient-mark-mode 1)

;; enables by default the math mode
(add-hook 'LaTeX-mode-hook 'LaTeX-math-mode)

;;-----------------
;; mode Cubicle
;;-----------------
(setq auto-mode-alist
      (cons '("\\.cub$" . cubicle-mode) auto-mode-alist))
(autoload 'cubicle-mode "cubicle-mode" "Major mode for Cubicle." t)

;;-----------------
;; mode NuSMV
;;-----------------
(setq auto-mode-alist
      (cons '("\\.smv$" . nusmv-mode) auto-mode-alist))
(autoload 'nusmv-mode "nusmv-mode" "Major mode for nuSMV." t)

;;-----------------
;; mode OCRA
;;-----------------
(setq auto-mode-alist
      (cons '("\\.oss$" . ocra-mode) auto-mode-alist))
(autoload 'ocra-mode "ocra-mode" "Major mode for OCRA." t)


;;-----------
;; mode LUSTRE
;; ----------

(setq auto-mode-alist (cons '("\\.mls$" . lustre-mode) auto-mode-alist))
(autoload 'lustre-mode "lustre" "Edition de code lustre" t)

;;-----------
;; mode MERCI
;; ----------

(setq auto-mode-alist
      (cons '("\\.mrc$" . merci-mode) auto-mode-alist))
(autoload 'merci-mode "merci-mode" "Major mode for Merci." t)

;;-----------
;; mode Why3
;; ----------

(setq auto-mode-alist
      (cons '("\\.\\(\\(mlw\\)\\|\\(why\\)\\)$" . why3-mode) auto-mode-alist))
(autoload 'why3-mode "why3-mode" "Major mode for Why3." t)

;; (setq auto-mode-alist
;;       (cons '("\\.cub" . tuareg-mode) auto-mode-alist))

(autoload 'tuareg-mode "tuareg" "Major mode for editing Caml code." t)
(autoload 'run-caml "inf-caml" "Run an inferior Caml process." t)
(autoload 'camldebug "camldebug" "Run the Caml debugger." t)

(defun my-set-tuareg-mode ()
  (when (and (stringp buffer-file-name)
             (string-match "\\.mly\\'" buffer-file-name))
    (tuareg-mode)
    (lambda () (electric-indent-local-mode -1))))

(add-hook 'find-file-hook 'my-set-tuareg-mode)

(if (and (boundp 'window-system) window-system)
    (require 'font-lock))

(add-hook
 'tuareg-mode-hook
 '(lambda ()
    (define-key tuareg-mode-map [f2] 'tuareg-eval-phrase)
    (define-key tuareg-mode-map [S-f2] 'tuareg-eval-until-point)
    (define-key tuareg-mode-map [f3] 'caml-types-show-type)))

(defun up-slightly () (interactive) (scroll-up 5))
(defun down-slightly () (interactive) (scroll-down 5))

(global-set-key [mouse-4]   'down-slightly)
(global-set-key [mouse-5]   'up-slightly)

(setq compilation-window-height 12)

;; (setq compilation-directory-matcher '("\\(?:Entering\\|Leavin\\(g\\)\\|\\) directory [`']\\(.+\\)'$" (2 . 1)))
(setq compilation-directory-matcher '("\\(?:on entre dans le\\|on quitte l\\(e\\)\\|\\) répertoire « \\(.+\\) »$" (2 . 1)))
(setq compilation-page-delimiter "\\(?:on entre dans le\\|on quitte l\\(e\\)\\|\\) répertoire « \\(.+\\) »$")

                                        ;(global-set-key [home] 'beginning-of-buffer)
                                        ;(global-set-key [end] 'end-of-buffer)

;; Montrer la correspondance des parenthèses (systématiquement et non seulement après la frappe)
(require 'paren)
(show-paren-mode 1)
(setq blink-matching-paren t)
(setq blink-matching-paren-on-screen t)
(setq show-paren-style 'expression)
(setq blink-matching-paren-dont-ignore-comments t)

(defun comment-dwim-line (&optional arg)
  "Replacement for the comment-dwim command.
        If no region is selected and current line is not blank and we are not at the end of the line,
        then comment current line.
        Replaces default behaviour of comment-dwim, when it inserts comment at the end of the line."
  (interactive "*P")
  (comment-normalize-vars)
  (if (and (not (region-active-p)) (not (looking-at "[ \t]*$")))
      (comment-or-uncomment-region (line-beginning-position) (line-end-position))
    (comment-dwim arg)))

;; (require 'smart-tab)
;; (global-smart-tab-mode 1)


;; ========== Enable Line and Column Numbering ==========

;; Show line-number in the mode line

;; Show column-number in the mode line
;; (column-number-mode 1)

;; Supprimer la selection
(delete-selection-mode 1)

;; ========== Shortcuts ================
(global-set-key "\M-;" 'comment-dwim-line)
;; (global-undo-tree-mode)

(global-set-key (kbd "C-<tab>") 'dabbrev-expand)
(define-key minibuffer-local-map (kbd "C-<tab>") 'dabbrev-expand)

;; (global-set-key [f1] 'ocaml-navigator-locate)

(global-set-key [f3] 'next-match)
(defun prev-match () (interactive nil) (next-match -1))
(global-set-key [(shift f3)] 'prev-match)
(global-set-key [backtab] 'auto-complete)

(global-set-key [f4]   'goto-line)
(global-set-key [f5]   'compile)
(global-set-key [f6]   'recompile)
(global-set-key [f7]   'next-error)
(global-set-key [f8]   'normal-mode)

(global-set-key (kbd "C-c t")   'caml-types-show-type)

(global-set-key (kbd "C-n") 'next-error)
(global-set-key (kbd "C-p") 'previous-error)

(global-set-key [(control delete)] 'kill-this-buffer)
(global-set-key [(meta g)] 'goto-line)

(defun up-slightly () (interactive) (scroll-up 5))
(defun down-slightly () (interactive) (scroll-down 5))

(global-set-key [mouse-4]   'down-slightly)
(global-set-key [mouse-5]   'up-slightly)

(global-set-key [end] 'end-of-buffer)
(global-set-key [home] 'beginning-of-buffer)

;; JCF
;; (global-set-key "\C-z"  '(lambda () (interactive) (scroll-up 1)))
;; (global-set-key "\ez"  '(lambda () (interactive) (scroll-down 1)))
(global-set-key (kbd "C-c C-g s") 'magit-status)
(put 'downcase-region 'disabled nil)

(defun set-ocaml-error-regexp ()
  (set
   'compilation-error-regexp-alist
   (list '("[Ff]ile \\(\"\\(.*?\\)\", line \\(-?[0-9]+\\)\\(, characters \\(-?[0-9]+\\)-\\([0-9]+\\)\\)?\\)\\(:\n\\(\\(Warning .*?\\)\\|\\(Error\\)\\):\\)?"
    2 3 (5 . 6) (9 . 11) 1 (8 compilation-message-face)))))

(add-hook 'tuareg-mode-hook 'set-ocaml-error-regexp)
(add-hook 'caml-mode-hook 'set-ocaml-error-regexp)

(add-to-list 'load-path
	     "/home/mattias/.opam/4.05.0/share/emacs/site-lisp/")

;; ## added by OPAM user-setup for emacs / base ## 56ab50dc8996d2bb95e7856a6eddb17b ## you can edit, but keep this line
(require 'opam-user-setup "~/.emacs.d/opam-user-setup.el")
;; ## end of OPAM user-setup addition for emacs / base ## keep this line
