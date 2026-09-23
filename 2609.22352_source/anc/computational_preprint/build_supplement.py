"""Assemble a self-contained local supplement without publishing anything."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import zipfile


ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    target = args.output
    if target.exists() or target.with_suffix('.zip').exists():
        raise FileExistsError(target)
    target.mkdir(parents=True)
    for src in sorted(ROOT.glob('*.py')):
        dst = target/'computational_preprint'/src.name
        dst.parent.mkdir(exist_ok=True)
        shutil.copy2(src,dst)
    for src in sorted(ROOT.glob('*.txt')):
        shutil.copy2(src,target/'computational_preprint'/src.name)
    for src in sorted(ROOT.glob('*.md')):
        shutil.copy2(src,target/'computational_preprint'/src.name)
    shutil.copy2(ROOT/'REPRODUCIBILITY.md',target/'README.md')
    for folder in ('results','manuscript_ru'):
        shutil.copytree(ROOT/folder,target/'computational_preprint'/folder,
                        ignore=shutil.ignore_patterns('__pycache__','build','*.pyc','.DS_Store'))
    pdf = ROOT/'manuscript_ru/build/painleve_contour_computation_ru.pdf'
    if pdf.is_file():
        shutil.copy2(pdf,target/'computational_preprint/manuscript_ru'/pdf.name)
    (target/'scripts').mkdir()
    for name in ('verify_piv_numerical.py','verify_piv_two_contours.py','verify_piv_symbolic.py'):
        shutil.copy2(ROOT.parent/'scripts'/name,target/'scripts'/name)
    manifest = {str(p.relative_to(target)):hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sorted(target.rglob('*')) if p.is_file()}
    (target/'MANIFEST.json').write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n')
    with zipfile.ZipFile(target.with_suffix('.zip'),'w',zipfile.ZIP_DEFLATED) as archive:
        for path in sorted(target.rglob('*')):
            if path.is_file():
                archive.write(path,str(Path(target.name)/path.relative_to(target)))
    print(f'{len(manifest)} files; {target.with_suffix(".zip")}')


if __name__ == '__main__':
    main()
