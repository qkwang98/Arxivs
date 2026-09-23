"""Generate table_main.tex from sun_final.json and sun_gcd.json."""
import json
fin=json.load(open('sun_final.json'))
gc={(r['B'],r['S']):r for r in json.load(open('sun_gcd.json'))}
def fmt(x): return f"{x:,.1f}".replace(',','{,}')
lines=[]
lines.append(r"\begin{table}[ht]\centering\footnotesize")
lines.append(r"\caption{Values from exact rational data with the definitions of \cite{Sun26}, $S=\lfloor B/20\rfloor$, and the row set $A$ giving the smallest $T_B=\log H_B+\log|\qhat_B(G)|$; logarithms are rounded to the displayed precision, with the certification of $\log|\qhat_B(G)|$ described in Section~\ref{sec:computation}. In every row $H_B$ is odd, and the listed coprime pair $(a,q)$ has $\gcd(H_B,\Phi(a,q))=1$ (Lemma~\ref{lem:cert}), so $\den(q^S\qhat_B(a/q))=H_B$ there. The rounding bound on $\log|\qhat_B(G)|$ is below $10^{-2700}$ relative in every row. The derivation in \cite{Sun26} would require $T_B\le-0.00966\,B^2+o(B^2)$.}\label{tab:main}")
lines.append(r"\begin{tabular}{@{}rrrrrrlrl@{}}\toprule")
lines.append(r"$B$ & $S$ & $\log H_B$ & $\log|\qhat_B(G)|$ & $T_B$ & $T_B/B^2$ & row set $A$ & $v_3(H_B)$ & $(a,q)$\\\midrule")
for r in fin:
    B,S=r['B'],r['S']; b=r['best']; g=gc.get((B,S),{})
    Astr=r"\{"+",".join(str(t) for t in b['A'])+r"\}"
    v3=g.get('v3_H',''); pr=g.get('pair',('',''))
    lines.append(f"{B} & {S} & {fmt(b['logH'])} & {fmt(b['logq'])} & {fmt(b['T'])} & {b['T']/B**2:.3f} & ${Astr}$ & {v3} & $({pr[0]},{pr[1]})$\\\\")
lines.append(r"\bottomrule\end{tabular}\end{table}")
open('table_main.tex','w').write("\n".join(lines)+"\n")
print("\n".join(lines[:6])); print("...", len(fin), "rows")
