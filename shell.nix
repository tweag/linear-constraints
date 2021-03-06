with { pkgs = import ./nix {}; };
pkgs.mkShell
  { buildInputs = with pkgs; [
      niv
      haskellPackages.lhs2tex
      biber
      ott
      inotify-tools
      pdftk
      (texlive.combine {
        inherit (texlive)
          # basic toolbox
          scheme-small
          cleveref
          latexmk biblatex
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

          # acmart and dependencies
          acmart totpages trimspaces
          libertine environ hyperxmp
          ifmtarg comment ncctools
          inconsolata newtx txfonts
          ;
      })

      ];

    FONTCONFIG_FILE = pkgs.makeFontsConf { fontDirectories =
    # Fonts for Xetex
    [ pkgs.libertine
      pkgs.inconsolata
    ]; };
}
