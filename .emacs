(require 'tramp)
(setq tramp-default-method "ssh")
(setq password-cache-expiry nil)

(require 'package) ;; You might already have this line
(add-to-list 'package-archives
             '("melpa" . "http://melpa.org/packages/") t)
;; (when (< emacs-major-version 24)
;;   ;; For important compatibility libraries like cl-lib
;;   (add-to-list 'package-archives '("gnu" . "http://elpa.gnu.org/packages/")))
(package-initialize) ;; You might already have this line

(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(ansi-color-names-vector ["#2e3436" "#a40000" "#4e9a06" "#c4a000" "#204a87" "#5c3566" "#729fcf" "#eeeeec"])
 '(browse-url-netscape-arguments nil)
 '(browse-url-netscape-program "firefox")
 '(browse-url-netscape-startup-arguments (quote ("-remote")))
 '(browse-url-netscape-version 4)
 '(column-number-mode 1)
 '(custom-enabled-themes (quote (tsdh-dark)))
 '(delete-selection-mode nil)
 '(inhibit-startup-screen t)
 ;; '(line-number-mode 1)
 '(nil nil t)
 '(safe-local-variable-values (quote ((TeX-master . "rapportM2R") (encoding . utf-8) (encoding . utf8) (TeX-master . "paper"))))
 '(scroll-bar-mode (quote right))
 '(text-mode-hook (quote (turn-on-auto-fill text-mode-hook-identify)))
 '(tool-bar-mode nil)
 '(tuareg-function-indent 2)
 '(tuareg-match-clause-indent 0)
 '(tuareg-use-abbrev-mode t)
 '(tuareg-with-indent 2)
 '(user-mail-address "roux@lri.fr")
 '(vm-delete-after-saving t))

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
 '(default ((t (:family "DejaVu Sans Mono" :foundry "unknown" :slant normal :weight normal :height 98 :width normal)))))

;; (setq-default tuareg-in-indent 0)
;; (setq tuareg-match-indent 2)
;; On peut enfin mettre un titre à la fenêtre (avant c'était : "emacs@login",
;; maintenant c'est : "nom_du_fichier (/home/login/..../nom_du_fichier)"
(setq frame-title-format '(buffer-file-name "%b (%f)" "%b"))

(setq load-path (cons "~/.emacs.d/" load-path))
;; (add-to-list 'load-path "~/tuareg-2.0.4") 
;; (add-to-list 'load-path "~/.opam/4.01.0/share/emacs/site-lisp")
;; (require 'ocp-indent)
;; (require 'ocp-index)
;; Add opam emacs directory to the load-path
(setq opam-share (substring (shell-command-to-string "opam config var share 2> /dev/null") 0 -1))
(add-to-list 'load-path (concat opam-share "/emacs/site-lisp"))
;; Load merlin-mode
;; (require 'merlin)


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
      smtpmail-smtp-server              "smtp.lri.fr")
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
;; mode Cubicle                                                             
;;-----------------                                                         
 (setq auto-mode-alist                                                      
       (cons '("\\.cub$" . cubicle-mode) auto-mode-alist))                  
 (autoload 'cubicle-mode "cubicle-mode" "Major mode for Cubicle." t)       

(setq compilation-scroll-output t)
;; (setq-default tuareg-in-indent 0)

;;------------------
;; AUCTEX
;;------------------

(setq TeX-auto-save t)
(setq TeX-parse-self t)
(setq-default TeX-master nil)

(add-hook 'LaTeX-mode-hook 'visual-line-mode)
(add-hook 'LaTeX-mode-hook 'flyspell-mode)
(add-hook 'LaTeX-mode-hook 'LaTeX-math-mode)

(add-hook 'LaTeX-mode-hook 'turn-on-reftex)
(setq reftex-plug-into-AUCTeX t)

(autoload 'flyspell-mode "flyspell" "On-the-fly spelling checker." t) 
(autoload 'flyspell-delay-command "flyspell" "Delay on command." t) 
(autoload 'tex-mode-flyspell-verify "flyspell" "" t) 

;; (require 'flyspell-lazy)

;; (flyspell-lazy-mode 1)

;; (flyspell-mode 1)      ; or (flyspell-prog-mode)

(add-hook 'LaTeX-mode-hook 'flyspell-mode) 

; reftex

;; (autoload 'reftex-mode               "reftex" "RefTeX Minor Mode" t)
;; (autoload 'turn-on-reftex            "reftex" "RefTeX Minor Mode" nil)
;; (setq reftex-plug-into-AUCTeX t
;;       reftex-save-parse-info t
;;       reftex-enable-partial-scans t)
;; ; Turn on RefTeX Minor Mode for all LaTeX files
;; (add-hook 'LaTeX-mode-hook 'turn-on-reftex)   ; with AUCTeX LaTeX mode


;--------------------------
; ISPELL
;--------------------------

;; (autoload 'ispell-word "ispell"
;;   "Check the spelling of word in buffer." t)
;; (global-set-key "\e$" 'ispell-word)
;; (autoload 'ispell-region "ispell"
;;   "Check the spelling of region." t)
;; (autoload 'ispell-buffer "ispell"
;;   "Check the spelling of buffer." t)
;; (autoload 'ispell-complete-word "ispell"
;;   "Look up current word in dictionary and try to complete it." t)
;; (autoload 'ispell-change-dictionary "ispell"
;;   "Change ispell dictionary." t)
;; (autoload 'ispell-message "ispell"
;;   "Check spelling of mail message or news post.")
;; (autoload 'ispell-minor-mode "ispell"
;;   "Toggle mode to automatically spell check words as they are typed in.")


;; (setq LaTeX-mode-hook
;;       '(lambda () "Défauts pour le mode SGML."
;; 	 (setq ispell-personal-dictionary "~/.ispell-dico-perso")
;; 	 (ispell-change-dictionary "francais")
;; 	 ))

;;------------------------
;; Anything and Lacarte
;;------------------------

;; (require 'anything-config)
;; (require 'lacarte)

;; (setq LaTeX-math-menu-unicode t)
;; (eval-after-load 'latex 
;;   '(define-key LaTeX-mode-map [C-tab] 'anything-math-symbols))

;; (defvar anything-c-source-lacarte-math
;;   '((name . "Math Symbols")
;;     (init . (lambda()
;;               (setq anything-c-lacarte-major-mode major-mode)))
;;     (candidates
;;      . (lambda () (if (eq anything-c-lacarte-major-mode 'latex-mode)
;;                       (delete '(nil) (lacarte-get-a-menu-item-alist LaTeX-math-mode-map)))))
;;     (action . (("Open" . (lambda (candidate)
;;                            (call-interactively candidate)))))))

;; (defun anything-math-symbols ()
;;   "Anything for searching math menus"
;;   (interactive)
;;   (anything '(anything-c-source-lacarte-math)
;;             (thing-at-point 'symbol) "Symbol: "
;;             nil nil "*anything math symbols*"))

;; predictive install location
;; (add-to-list 'load-path "~/.emacs.d/predictive/")
;; ;; dictionary locations
;; (add-to-list 'load-path "~/.emacs.d/predictive/latex/")
;; (add-to-list 'load-path "~/.emacs.d/predictive/texinfo/")
;; (add-to-list 'load-path "~/.emacs.d/predictive/html/")
;; (add-to-list 'load-path "~/.emacs.d/predictive/dictionnaires/")

;; load predictive package
;; (autoload 'predictive-mode "~/.emacs.d/predictive/predictive"
;;   "Turn on Predictive Completion Mode." t)

;; (add-hook 'LaTeX-mode-hook 'predictive-mode)
;; (setq predictive-main-dict 'dict-latex)
 
;; (set-default 'predictive-auto-add-to-dict t)
;; (setq predictive-auto-learn t
;;       predictive-add-to-dict-ask nil
;;       predictive-use-auto-learn-cache nil
;;       predictive-which-dict t
;;       completion-ui-use-hotkeys nil)
;; Use space and punctuation to accept the current the most likely completion
;; (setq auto-completion-syntax-alist (quote (global accept . word))) 
;; Avoid completion for short trivial words
;; (setq auto-completion-min-chars (quote (global . 2))) 
;;----------
;; mode CAML
;;----------

(setq auto-mode-alist
      (cons '("\\.ml[iylp]?" . tuareg-mode) auto-mode-alist))
(autoload 'tuareg-mode "tuareg" "Major mode for editing Caml code." t)
(autoload 'run-caml "inf-caml" "Run an inferior Caml process." t)
(autoload 'camldebug "camldebug" "Run the Caml debugger." t)

(if (and (boundp 'window-system) window-system)
    (require 'font-lock))

(add-hook
 'tuareg-mode-hook
 '(lambda ()
    (define-key tuareg-mode-map [f2] 'tuareg-eval-phrase)
    (define-key tuareg-mode-map [S-f2] 'tuareg-eval-until-point)
    (define-key tuareg-mode-map [f3] 'caml-types-show-type)))

(setq-default indent-tabs-mode nil)

(defun up-slightly () (interactive) (scroll-up 5))
(defun down-slightly () (interactive) (scroll-down 5))

(global-set-key [mouse-4]   'down-slightly)
(global-set-key [mouse-5]   'up-slightly)

(setq compilation-window-height 12)

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
