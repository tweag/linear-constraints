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

          # acmart and dependencies
          acmart totpages trimspaces
          libertine environ hyperxmp
          ifmtarg comment ncctools
          inconsolata # newtx
          # acmart warns if newtx is absent, but it conflicts with
          # amssymb. So let's leave it out for now.
          ;
      })

      ];

    FONTCONFIG_FILE = pkgs.makeFontsConf { fontDirectories =
    # Fonts for Xetex
    [ pkgs.libertine
      pkgs.inconsolata
    ]; };
}
