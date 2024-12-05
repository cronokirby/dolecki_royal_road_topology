build:
    lake build

build-docs:
    lake -R -Kenv=dev build DoleckiRoyalRoadTopology:docs

serve-docs:
    caddy file-server --listen :1234 --root .lake/build/doc/