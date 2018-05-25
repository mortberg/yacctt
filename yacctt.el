;;; yacctt.el --- Mode for cartesian cubical type theory -*- lexical-binding: t -*-
;; URL: https://github.com/mortberg/yacctt
;; Package-version: 1.0
;; Package-Requires: ((emacs "24.1") (cl-lib "0.5"))
;; Keywords: languages

;; This file is not part of GNU Emacs.

;; Copyright (c) 2018 Anders Mörtberg and Carlo Angiuli

;; Permission is hereby granted, free of charge, to any person obtaining
;; a copy of this software and associated documentation files (the
;; "Software"), to deal in the Software without restriction, including
;; without limitation the rights to use, copy, modify, merge, publish,
;; distribute, sublicense, and/or sell copies of the Software, and to
;; permit persons to whom the Software is furnished to do so, subject to
;; the following conditions:

;; The above copyright notice and this permission notice shall be included
;; in all copies or substantial portions of the Software.

;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

;;; Commentary:
;; This package provides a major mode for editing proofs or programs
;; in yacctt, an experimental implementation of cartesian cubical type
;; theory.


;;; Code:

(require 'comint)
(require 'cl-lib)

;;;; Customization options

(defgroup yacctt nil "Options for yacctt-mode for cartesian cubical type theory"
  :group 'languages
  :prefix 'yacctt-
  :tag "Cartesian cubical type theory")

(defcustom yacctt-command "yacctt"
  "The command to be run for yacctt."
  :group 'yacctt
  :type 'string
  :tag "Command for yacctt"
  :options '("yacctt" "cabal exec yacctt"))

;;;; Syntax

(defvar yacctt-keywords
  '("hdata" "data" "import" "mutual" "let" "in" "split"
    "with" "module" "where" "U" "opaque" "transparent" "transparent_all")
  "Keywords for yacctt.")

(defvar yacctt-special
  '("undefined" "primitive")
  "Special operators for yacctt.")

(defvar yacctt-keywords-regexp
  (regexp-opt yacctt-keywords 'words)
  "Regexp that recognizes keywords for yacctt.")

(defvar yacctt-operators-regexp
  (regexp-opt '(":" "->" "=" "|" "\\" "*" "_" "<" ">" "\\/" "/\\" "-" "@") t)
  "Regexp that recognizes operators for yacctt.")

(defvar yacctt-special-regexp
  (regexp-opt yacctt-special 'words)
  "Regexp that recognizes special operators for yacctt.")

(defvar yacctt-def-regexp "^[[:word:]']+"
  "Regexp that recognizes the beginning of a yacctt definition.")

(defvar yacctt-font-lock-keywords
  `((,yacctt-keywords-regexp . font-lock-type-face)
    (,yacctt-operators-regexp . font-lock-variable-name-face)
    (,yacctt-special-regexp . font-lock-warning-face)
    (,yacctt-def-regexp . font-lock-function-name-face))
  "Font-lock information, assigning each class of keyword a face.")

(defvar yacctt-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\{  "(}1nb" st)
    (modify-syntax-entry ?\}  "){4nb" st)
    (modify-syntax-entry ?-  "_ 123" st)
    (modify-syntax-entry ?\n ">" st)
    (modify-syntax-entry ?\\ "." st)
    st)
  "The syntax table for yacctt, with Haskell-style comments.")


;;;; The interactive toplevel

(defvar yacctt-cubical-process nil
  "The subprocess buffer for yacctt.")

(defvar yacctt-loaded-buffer nil
  "The currently-loaded buffer for yacctt.

If no buffer is loaded, then this variable is nil.")

(defun yacctt-ensure-process ()
  "Ensure that a process is running for yacctt and return the process buffer."
  (if (and yacctt-cubical-process (get-buffer-process yacctt-cubical-process))
      yacctt-cubical-process
    (let ((process (make-comint "yacctt" yacctt-command)))
      (setq yacctt-cubical-process process)
      process)))

(defun yacctt-load ()
  "Start yacctt if it is not running, and get the current buffer loaded."
  (interactive)
  (let ((file (buffer-file-name)))
    (unless file
      (error "The current buffer is not associated with a file"))
    (let ((yacctt-proc (yacctt-ensure-process))
          (dir (file-name-directory file))
          (f (file-name-nondirectory file)))
      (save-buffer)
      ;; Get in the right working directory. No space-escaping is
      ;; necessary for yacctt, which in fact expects filenames to be
      ;; written without quotes or space-escaping.
      (comint-send-string yacctt-proc (concat ":cd " dir "\n"))
      ;; Load the file
      (comint-send-string yacctt-proc (concat ":l " f "\n"))
      ;; Show the buffer
      (pop-to-buffer yacctt-proc '(display-buffer-use-some-window (inhibit-same-window . t))))))

;;;; Completion support

(defvar yacctt--completion-regexp
  "^\\(?1:[[:word:]']+\\) [:(]\\|^data \\(?1:[[:word:]']+\\)\\|=\\s-*\\(?1:[[:word:]']\\)\\||\\s-*\\(?1:[[:word:]']\\)"
  "Regexp for finding names to complete.

This regexp matches the following kinds of strings:

<NAME> :
<NAME> (
data <NAME>
= <NAME>
| <NAME>

It is overly liberal, but it is better to have too many
suggestions for completion rather than too few.")

(defun yacctt-defined-names ()
  "Find all names defined in this buffer."
  (save-excursion
    (let (names)
      (goto-char (point-min))
      (while (re-search-forward yacctt--completion-regexp nil t)
        ;; Do not save if inside comment
        (unless (nth 4 (syntax-ppss))
          (push (match-string-no-properties 1) names)))
      names)))

(defun yacctt-completion-at-point ()
  "Attempt to perform completion for yacctt's keywords and the definitions in this file."
  (when (looking-back "\\w+" nil t)
    (let* ((match (match-string-no-properties 0))
           (start-pos (match-beginning 0))
           (end-pos (match-end 0))
           (candidates (cl-remove-if-not
                        (apply-partially #'string-prefix-p match)
                        (append yacctt-keywords
                                yacctt-special
                                (yacctt-defined-names)))))
      (if (null candidates)
          nil
        (list start-pos end-pos candidates)))))

;;;; The mode itself

;;;###autoload
(define-derived-mode yacctt-mode prog-mode
  "ytt"
  "Major mode for editing yacctt type theory files."

  :syntax-table yacctt-syntax-table

  ;; Make comment-dwim do the right thing for Yacctt
  (set (make-local-variable 'comment-start) "--")
  (set (make-local-variable 'comment-end) "")

  ;; Code for syntax highlighting
  (setq font-lock-defaults '(yacctt-font-lock-keywords))

  ;; Bind mode-specific commands to keys
  (define-key yacctt-mode-map (kbd "C-c C-l") 'yacctt-load)

  ;; Install the completion handler
  (set (make-local-variable 'completion-at-point-functions)
       '(yacctt-completion-at-point))

  ;; Setup imenu, to allow tools such as imenu and Helm to jump
  ;; directly to names in the current buffer.
  (set (make-local-variable 'imenu-generic-expression)
       '(("Definitions" "^\\(?1:[[:word:]']+\\) *[:(]" 1)
         ("Datatypes" "^\\s-*data\\s-+\\(?1:[[:word:]']+\\)" 1)))

  ;; Clear memory
  (setq yacctt-keywords-regexp nil)
  (setq yacctt-operators-regexp nil)
  (setq yacctt-special-regexp nil))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.ytt\\'" . yacctt-mode))

(provide 'yacctt)
;;; yacctt.el ends here
