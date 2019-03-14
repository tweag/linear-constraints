with { pkgs = import ./nix {}; };
pkgs.mkShell
  { buildInputs = with pkgs; [
      niv
      haskellPackages.lhs2tex
      biber
      (texlive.combine {
        inherit (texlive)
          scheme-small
          latexmk
          stmaryrd lazylist polytable # for lhs2tex
          biblatex
          unicode-math;
      })

      ];
  }
