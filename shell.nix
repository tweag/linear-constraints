with { pkgs = import ./nix {}; };
pkgs.mkShell
  { buildInputs = with pkgs; [
      niv
      haskellPackages.lhs2tex
      biber
      ott
      inotify-tools
      (texlive.combine {
        inherit (texlive)
          scheme-small
          latexmk biblatex
          stmaryrd lazylist polytable # for lhs2tex
          unicode-math lm lm-math
          logreq xstring
          xargs todonotes
          mathpartir;
      })

      ];
  }
