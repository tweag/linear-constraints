with { pkgs = import ./nix {}; };
pkgs.mkShell
  { buildInputs = with pkgs; [
      haskellPackages.lhs2tex
      biber
      ott
      pdftk
      entr
      (texlive.combine {
        inherit (texlive)
          # basic toolbox
          scheme-small
          cleveref
          latexmk
          biblatex biblatex-software
          stmaryrd
          unicode-math lm lm-math
          logreq xstring
          xargs todonotes
          mathpartir
          newunicodechar

          # for lhs2tex
          lazylist polytable

          # for ott
          supertabular

          # jfp dependencies
          soul framed tex-gyre

          # don't know why but needed
          # TODO
          newtx txfonts fontaxes breakurl
          ;
      })

      ];
  }
