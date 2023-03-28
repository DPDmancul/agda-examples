{ pkgs ? import <nixpkgs> {} }:
(import ./shell.nix { inherit pkgs; }).overrideAttrs (oldAttrs: {
  nativeBuildInputs = with pkgs; oldAttrs.nativeBuildInputs ++ [
    (symlinkJoin {
      name = "emacs";
      paths = [ (emacs-nox.pkgs.withPackages (epkgs: [ epkgs.evil epkgs.evil-terminal-cursor-changer ])) ];
      buildInputs = [ makeWrapper ];
      postBuild = ''
        wrapProgram $out/bin/emacs \
        --add-flags "-q --load '${pkgs.writeText ".emacs" ''
          (load-file (let ((coding-system-for-read 'utf-8)) (shell-command-to-string "agda-mode locate")))
          (add-to-list 'auto-mode-alist '("\\.lagda.md" . agda2-mode))

          (setq-default indent-tabs-mode nil)

          (menu-bar-mode -1)

          (unless (display-graphic-p))
            (progn (set-terminal-parameter nil 'background-mode 'light)
                   ;;(load-theme 'tsdh-light)
                   )

          (custom-set-variables
            '(xterm-mouse-mode t)
            '(inhibit-startup-screen t))

          (global-set-key (kbd "C-c C-v") 'agda2-compute-normalised-maybe-toplevel)
          (add-hook 'agda2-mode-hook
                    #'(lambda () (define-key (current-local-map) (kbd "C-u") (lookup-key (current-local-map) (kbd "C-c")))
                                 ;; support for terminal
                                 (define-key (current-local-map) (kbd "C-c ,") (lookup-key (current-local-map) (kbd "C-c C-,")))
                                 (define-key (current-local-map) (kbd "C-c .") (lookup-key (current-local-map) (kbd "C-c C-.")))
                                 (display-line-numbers-mode)
                                 (setq display-line-numbers 'relative)
                                 (evil-insert-state)
                                 (activate-input-method "Agda")
                    ))

          (run-with-idle-timer 60 t #'(lambda () (save-some-buffers t nil)))

          (require 'evil)
          (setq evil-want-fine-undo 't)
          (evil-mode 1)
          (unless (display-graphic-p)
            (require 'evil-terminal-cursor-changer)
            (evil-terminal-cursor-changer-activate))
          (setq evil-insert-state-cursor 'bar)
        ''}'"
      '';
    })
  ];
})

