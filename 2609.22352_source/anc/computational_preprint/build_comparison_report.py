#!/usr/bin/env python3
"""Render the saved experiment, without rerunning or changing its results."""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent
CASES = ("original", "second")
STYLES = (
    ("RK45_1e-09", "RK45, tol=1e-9", "--"),
    ("RK45_1e-12", "RK45, tol=1e-12", ":"),
    ("balanced_contour_3e-13_R4.8", "Scaled contours, R=4.8", "-."),
    ("balanced_contour_3e-13_R6", "Scaled contours, R=6", "-"),
)


def nonzero(values):
    return np.where(values > 0, values, np.nan)


def main():
    plt.rcParams.update({"font.size": 10, "axes.spines.top": False,
                         "axes.spines.right": False, "savefig.dpi": 170})
    fig, axes = plt.subplots(2, 2, figsize=(10, 7), layout="constrained")
    convergence, caxes = plt.subplots(1, 2, figsize=(10, 3.6), layout="constrained")
    text = ["# Контурный метод и Рунге–Кутта: первый вычислительный эксперимент", "",
            "Выполнены расчёты на двух комплексных фонах при фиксированных параметрах Пенлеве. "
            "Это предварительное исследование, а не готовый препринт или гарантированная оценка ошибок.", "",
            "## Постановка", "",
            "На сетке из 33 точек, x=x0+s, -0.24 <= s <= 0.24, построена матрица "
            "F(x0)=I для переменных (y,y'). Оба начальных направления проверяются одновременно. "
            "Первый фон соответствует исходной статье; интервал расширен в пять раз. "
            "Второй фон имеет другие начальные q и p при тех же x0 и параметрах.", "",
            "Обозначения: h=2p-x-q/2, q'=q(2h+q+2x). Целевая нормальная форма: "
            "y''=U(x)y, где U=x²-(2theta_infinity-1)+6xq+15q²/4+12theta0²/q². "
            "Штрих означает производную по x, совпадающую с производной по вещественному смещению s. "
            "Столбцы F состоят из y и y' для начальных направлений (1,0) и (0,1).", "",
            "Сравниваются RK45 и контурные квадратуры, с исходным и масштабированным "
            "представлением столбцов пары Лакса. Общий нелинейный фон вычисляется DOP853 "
            "с относительным допуском 3e-14. Контрольная матрица решения получена DOP853 "
            "с тем же допуском. Она является численным ориентиром, а не точным решением.", "",
            "В каждой точке заново вычисляются четыре инвариантных произведения "
            "m=(s1*s2,s2*s3,s3*s4,s1*s4) и их производные по q,h. Произведения избыточны: "
            "они связаны алгебраическими соотношениями и не являются четырьмя независимыми интегралами.", "",
            "Производные вычислены двумя способами: интегрированием вариационной спектральной "
            "системы и квадратурой формулы вариации постоянных. Во втором способе используется "
            "терминально нормированный сопряжённый перенос: W'(t)=-W(t)A(t), W(1)=I, "
            "и delta u(1)=W(0)delta u(0)+integral W(t)delta A(t)u(t)dt. "
            "Здесь A(t) включает производную спектрального пути. Учтены вариации начальной "
            "формальной асимптотики и последующих нормировок определителей. Это конечные "
            "усечённые интегралы с асимптотическими начальными данными второго порядка; "
            "бесконечные секторные примитивы не вычисляются без усечения.", "",
            "Для перевода в вариации фона используется delta q=sqrt(q)y и "
            "delta h=y'/(2sqrt(q))-[q'/(4q sqrt(q))+sqrt(q)/2]y. "
            "Полученная матрица J_y(x) преобразует (y,y') в delta m. "
            "Проверяемая величина: J_y(x)F(x)-J_y(x0). Постоянство не навязывается алгоритмом.", "",
            "## Метрики", "",
            "Норма здесь означает максимум модулей элементов матрицы, а не спектральную норму. "
            "Ошибка F нормирована максимумом этой нормы контрольного решения на всей сетке. "
            "Дрейф delta m нормирован нормой J_y(x0). Дрейф вронскиана равен max|det F-1|. "
            "В таблицах приведены глобальные показатели по обоим начальным направлениям; "
            "значения отдельных компонент сохранены в CSV.", "",
            "Допуски разных алгоритмов не равнозначны достигаемой точности. "
            "Время построения F включает для контурного метода продолжение столбцов пары Лакса, "
            "выбор коэффициентов циклов и квадратуры. Общий фон и диагностика монодромии "
            "учитываются отдельно. Время измерено однократно; это не статистический бенчмарк.", ""]
    for row, case in enumerate(CASES):
        folder = HERE/"results"/f"{case}_integral_monitor_33"
        report = json.loads((folder/"results.json").read_text())
        data = np.load(folder/"arrays.npz")
        grid, jac, ref = data["grid"], data["jacobian"], data["reference"]
        center = len(grid)//2
        baseline = np.max(abs(jac[center]))
        for key, label, style in STYLES:
            matrix = data[key]
            drift = np.max(abs(jac @ matrix-jac[center]), axis=(1, 2))/baseline
            error = np.max(abs(matrix-ref), axis=(1, 2))/np.max(abs(ref))
            axes[row, 0].semilogy(grid, nonzero(error), style, color="black", label=label)
            axes[row, 1].semilogy(grid, nonzero(drift), style, color="black", label=label)
        floor = np.max(abs(jac @ ref-jac[center]), axis=(1, 2))/baseline
        axes[row, 1].semilogy(grid, nonzero(floor), "o", color="0.5", markersize=3,
                              label="Monitor on reference")
        for col, title in enumerate(("Solution error", "Monodromy variation drift")):
            axes[row, col].set(title=f"{case.capitalize()} background: {title}", xlabel="s = x - x0")
            axes[row, col].grid(True, alpha=.2)
        radius_rows = sorted([r for r in report["comparisons"] if
                              r["method"] == "balanced_contour" and r["tolerance"] == 3e-13],
                             key=lambda r: r["radius"])
        caxes[row].semilogy([r["radius"] for r in radius_rows],
                            [r["monodromy_variation_drift"] for r in radius_rows],
                            "ko-", label="Monodromy drift")
        caxes[row].semilogy([r["radius"] for r in radius_rows],
                            [r["solution_error_vs_dop853"] for r in radius_rows],
                            "ks--", label="Solution error")
        caxes[row].set(title=f"{case.capitalize()} background", xlabel="Contour truncation radius R")
        caxes[row].grid(True, alpha=.2)
        caxes[row].legend()
        initial_text = "; ".join(f"{name} = {complex(*value):g}" for name, value in report["initial_data"].items())
        text += [f"## Фон {row+1}: {case}", "", f"Начальные данные: {initial_text} (j обозначает мнимую единицу).", "",
                 "| Метод | Допуск | Радиус | Ошибка F | Дрейф delta m | Дрейф W | Время F, с |",
                 "|---|---:|---:|---:|---:|---:|---:|"]
        for r in report["comparisons"]:
            text.append(f"| {r['method']} | {r['tolerance']:.1e} | {r.get('radius', '-')} "
                        f"| {r['solution_error_vs_dop853']:.3e} | {r['monodromy_variation_drift']:.3e} "
                        f"| {r['wronskian_drift']:.3e} | {r['seconds']:.4f} |")
        text += ["", "### Контроль диагностики", "",
                 "| Радиус / допуск / способ | Дрейф m | Дрейф приведённых s | Дрейф delta m на контрольном решении | Время, с |",
                 "|---|---:|---:|---:|---:|"]
        for name, d in report["spectral_profiles"].items():
            text.append(f"| {name} | {d['base_invariant_drift']:.3e} | {d['corrected_stokes_drift']:.3e} "
                        f"| {d['reference_variation_drift']:.3e} | {d['seconds']:.3f} |")
        corrected_s = data["stokes_R7.2_tol2e-13_quadrature"]
        z = corrected_s[:, 0]/corrected_s[center, 0]
        predicted_s = corrected_s[center]*np.column_stack([z, 1/z, z, 1/z])
        gauge_fit = np.max(abs(corrected_s-predicted_s))/np.max(abs(corrected_s[center]))
        text += ["", f"Расхождение двух способов расчёта J: {report['quadrature_vs_variational_ode_jacobian']:.3e}.",
                 f"Остаток описания дрейфа отдельных множителей одним диагональным калибровочным множителем: {gauge_fit:.3e}.",
                 f"Изменение контрольной F при допусках DOP853 1e-12 и 3e-14: {report['reference_tolerance_check']:.3e}.",
                 f"Проверка чувствительности конечными разностями: `{report['sensitivity_finite_difference_errors']}`.",
                 f"На дополнительной сетке из 1001 точки min Re(q)={report['sampled_min_real_q']:.6g}; "
                 "использованная ветвь sqrt(q) согласована на этих точках. Это не интервальное доказательство отсутствия нулей/полюсов.", ""]
        residual_table = {}
        evaluation = grid[::4][2:-2]
        theta0 = complex(*report["initial_data"]["theta0"])
        theta_inf = complex(*report["initial_data"]["theta_infinity"])
        x0 = complex(*report["initial_data"]["x0"])
        text += ["### Разностная невязка", "",
                 "Использована пятиузловая формула четвёртого порядка для второй производной. "
                 "Во всех трёх сетках максимум берётся на одних и тех же пяти внутренних точках. "
                 "Невязка нормирована максимумом модулей двух членов уравнения на этих точках.", "",
                 "| Решение | Шаг 0.06 | Шаг 0.03 | Шаг 0.015 |", "|---|---:|---:|---:|"]
        for label in ("reference", "RK45_1e-09", "balanced_contour_3e-13_R6"):
            residuals = []
            for stride in (4, 2, 1):
                t = grid[::stride]
                q = data["background"][::stride, 0][2:-2]
                values = data[label][::stride, 0, :]
                step = t[1]-t[0]
                second = (-values[4:]+16*values[3:-1]-30*values[2:-2]
                          +16*values[1:-3]-values[:-4])/(12*step*step)
                x = x0+t[2:-2]
                potential = x*x-(2*theta_inf-1)+6*x*q+15*q*q/4+12*theta0*theta0/(q*q)
                term = potential[:, None]*values[2:-2]
                mask = np.any(np.isclose(t[2:-2, None], evaluation[None, :], atol=1e-14, rtol=0), axis=1)
                error = np.max(abs(second[mask]-term[mask]))/max(np.max(abs(second[mask])), np.max(abs(term[mask])))
                residuals.append(float(error))
            residual_table[label] = residuals
            text.append(f"| {label} | " + " | ".join(f"{v:.3e}" for v in residuals)+" |")
        text += ["", "Сходная невязка разных точных решений на одной сетке может определяться "
                 "разностным дифференцированием. Поэтому ошибка F и дрейф монодромии приведены отдельно.", ""]
        (folder/"derived_diagnostics.json").write_text(json.dumps({"gauge_fit_residual": float(gauge_fit),
            "finite_difference_steps": [.06, .03, .015], "relative_residuals": residual_table}, indent=2)+"\n")
    axes[0, 0].legend(fontsize=8)
    axes[0, 1].legend(fontsize=8)
    fig.savefig(HERE/"results/monodromy_comparison.png")
    convergence.savefig(HERE/"results/radius_convergence.png")
    plt.close("all")
    text += ["## Выводы и ограничения", "",
             "1. Дрейф вариаций монодромии различает точность численных решений и уменьшается при уточнении RK45.",
             "2. Постоянное по x масштабирование начальных столбцов сохраняет точную нормированную матрицу F, "
             "но существенно меняет численную ошибку контурного алгоритма. Это отдельный вычислительный эффект.",
             "3. После масштабирования увеличение радиуса усечения улучшает результат до уровня, "
             "на котором существенны остальные ошибки. Для контурного метода проведён отдельный радиусный ряд.",
             "4. На исследованных коротких интервалах RK45 достигает высокой точности значительно быстрее "
             "данной реализации контурного метода. Универсальное преимущество контурного метода не установлено.",
             "5. Дрейф монодромии на контрольном решении и расхождение способов вычисления J являются "
             "эмпирическими диагностическими уровнями, не гарантированной верхней границей ошибки. "
             "Отдельные исходные множители Стокса могут иметь иной масштаб ошибок, чем их инвариантные произведения.",
             "В частности, заметный дрейф приведённых множителей совместим с остаточным диагональным "
             "сопряжением: нижние множители меняются общим фактором z, верхние — обратным. "
             "Приведённая выше проверка использует z=s1(x)/s1(x0) только для диагностики, "
             "не для исправления данных или навязывания закона сохранения. Уменьшение этого дрейфа "
             "при увеличении R согласуется с влиянием усечения амплитудной асимптотики. "
             "Для подтверждения причины нужен отдельный ряд по порядку асимптотики.",
             "6. Здесь фиксирован второй порядок начальной асимптотики. Сходимость по её порядку, "
             "произвольная точность, более длинные области и трудные фоны остаются отдельными экспериментами. "
             "Полные матрицы связи и их вариации пока не включены в это сравнение.",
             "7. Большие абсолютные оценки ошибок отдельных квадратур в масштабированном базисе "
             "относятся к ненормированным интегралам. Они не являются оценкой ошибки F после обращения начальной матрицы.", "",
             "## Воспроизведение", "", "Команды приведены в README_RU.md. Таблицы и полные комплексные "
             "массивы находятся в results/original_integral_monitor_33 и results/second_integral_monitor_33. "
             "Архивы для Studies, исходный текст статьи и прежняя папка verification не изменялись; "
             "их контрольные суммы проверены каждым запуском.", "",
             "![Сравнение решений и монодромии](results/monodromy_comparison.png)", "",
             "![Сходимость по радиусу](results/radius_convergence.png)", ""]
    (HERE/"PILOT_REPORT_RU.md").write_text("\n".join(text))
    print(HERE/"PILOT_REPORT_RU.md")


if __name__ == "__main__":
    main()
