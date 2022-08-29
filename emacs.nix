{ pkgs ? import <nixpkgs> {} }:
(import ./shell.nix { inherit pkgs; }).overrideAttrs (oldAttrs: {
  nativeBuildInputs = with pkgs; oldAttrs.nativeBuildInputs ++ [
    (symlinkJoin {
      name = "emacs";
      paths = [ (emacs-nox.pkgs.withPackages (epkgs: [ epkgs.evil ])) ];
      buildInputs = [ makeWrapper ];
      postBuild = ''
        wrapProgram $out/bin/emacs \
        --add-flags "-q --load '${pkgs.writeText ".emacs" ''
          (load-file (let ((coding-system-for-read 'utf-8)) (shell-command-to-string "agda-mode locate")))

          (setq-default indent-tabs-mode nil)

          (if (not (display-graphic-p))
              (progn (set-terminal-parameter nil 'background-mode 'light)
                     ;;(load-theme 'tsdh-light)
                     ))

          (custom-set-variables
            '(xterm-mouse-mode t)
            '(inhibit-startup-screen t))

          (global-set-key (kbd "C-c C-v") 'agda2-compute-normalised-maybe-toplevel)
          (add-hook 'agda2-mode-hook
                    #'(lambda () (define-key (current-local-map) (kbd "C-u") (lookup-key (current-local-map) (kbd "C-c")))))

          (run-with-idle-timer 60 t #'(lambda () (save-some-buffers t nil)))

          (require 'evil)
          (setq evil-want-fine-undo 't)
          (evil-mode 1)
        ''}'"
      '';
    })
  ];
})

