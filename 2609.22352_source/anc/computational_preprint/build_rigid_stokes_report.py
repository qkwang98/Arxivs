"""Build the report and monochrome figure from the completed rigid PII run."""
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpmath import mp
import numpy as np

import rigid_monodromy as r


ROOT = Path(__file__).resolve().parent


def matrix(raw):
    return mp.matrix([[mp.mpc(*v) if isinstance(v, list) else mp.mpf(v)
                       for v in row] for row in raw])


def number(value):
    return f'{float(value):.3e}'


def complex_number(value, digits):
    if abs(mp.im(value)) < mp.mpf('1e-20')*abs(value):
        return mp.nstr(mp.re(value), digits)
    return mp.nstr(value, digits).replace('j', 'i')


def main():
    data = json.loads((ROOT/'results/rigid_stokes_e02/results.json').read_text())
    if data['status'] != 'complete' or not data['protected_unchanged']:
        raise ValueError('The calculation must be complete and the sources unchanged')
    mp.dps = 100
    offsets = data['offsets']
    initial = data['monitor']['0.0']
    j0 = matrix(initial['J'])
    weights = [max(abs(j0[j, k]) for k in range(2)) for j in range(4)]
    conditions = []
    for offset in offsets:
        j = matrix(data['monitor'][str(offset)]['J'])
        scaled = np.array([[complex(j[row, col]/weights[row]) for col in range(2)]
                           for row in range(4)])
        sigma = np.linalg.svd(np.vstack((scaled.real, scaled.imag)), compute_uv=False)
        conditions.append((offset-7, sigma[0], sigma[-1], sigma[0]/sigma[-1]))

    comparison = []
    details = []
    for tolerance, contour in data['contours'].items():
        pair = data['pairs'][tolerance]
        if not pair['matched']:
            raise ValueError('The matched-error comparison did not converge')
        rk = data['rk_trials'][pair['rk_tolerance']]
        for name, tol, item in [('Контур', tolerance, contour),
                                ('Рунге–Кутта', pair['rk_tolerance'], rk)]:
            comparison.append(f"| {name} | {tol} | {number(item['max_solution_error'])} | "
                              f"{number(item['max_row_variation_drift'])} | "
                              f"{number(item['max_wronskian_error'])} | {item['seconds']:.2f} |")
            rows = [max(p['row_variation_drift'][j] for p in item['points']) for j in range(4)]
            details.append(f"| {name}, {tol} | " + ' | '.join(number(v) for v in rows) + ' |')
    baseline = data['rk_trials']['1.0e-12']
    floor = data['reference_monitor']['max_row_variation_drift']
    refinements = data['monitor_refinements']
    checks = {
        'Уточнение опорной матрицы F': data['reference']['refinement_error'],
        'Дрейф самих коэффициентов Стокса': max(data['stokes_relative_drift_by_row']),
        'Дрейф J(t)F_ref(t)': floor,
        'Изменение строк J при уточнении спектрального расчёта':
            max(v for record in refinements.values() for v in record['J_row_relative']),
        'Отклонение соседних определителей от знака (-1)^j':
            max(mp.mpf(v['diagnostic']['adjacent_error']) for v in data['monitor'].values()),
    }
    for tol, item in data['contours'].items():
        for field, name in [('direction_error', 'Ошибка направления столбца'),
                            ('inner_boundary_error', 'Невязка сопряжения контуров'),
                            ('anchor_unitarity_error', 'Невязка унитарности переноса')]:
            checks[f'{name}, контур {tol}'] = max(mp.mpf(v[field]) for v in item['diagnostics'].values())

    ref = r.Reference(epsilon=data['epsilon'])
    times = np.linspace(-7, -1, 601)
    background = np.array([float(ref.at(mp.mpf(float(t)))[0]) for t in times])
    gain = np.array([np.linalg.svd(np.array(ref.matrix(mp.mpf(float(t))).tolist(), dtype=float),
                                  compute_uv=False)[0] for t in times])
    plt.rcParams.update({'font.size': 9, 'axes.grid': True, 'grid.color': '.85',
                         'grid.linewidth': .5, 'axes.spines.top': False,
                         'axes.spines.right': False, 'savefig.facecolor': 'white'})
    fig, axes = plt.subplots(2, 2, figsize=(10, 6.6), constrained_layout=True)
    axes[0, 0].plot(times, background, color='black', linewidth=1.2)
    axes[0, 0].set(title=r'(a) Rigid-loss background, $\epsilon=0.2$', ylabel=r'$u(t)$')
    axes[0, 1].semilogy(times, gain, color='black', linewidth=1.2)
    axes[0, 1].set(title='(b) Tangent amplification', ylabel=r'$\sigma_{\max}(F(t))$')
    for ax, (tol, item), label in zip(axes[1], data['contours'].items(), ['c', 'd']):
        rk = data['rk_trials'][data['pairs'][tol]['rk_tolerance']]
        for record, style, marker, name in [(item, '-', 'o', 'Contour'),
                                           (rk, '--', 's', 'RK 5(4)')]:
            points = record['points'][1:]
            ax.semilogy([p['t'] for p in points], [p['max_row_variation_drift'] for p in points],
                        color='black', linestyle=style, marker=marker, markersize=4,
                        markerfacecolor='white', label=name)
        ax.set(title=f"({label}) Matched solution error: {item['max_solution_error']:.1e}",
               ylabel=r'$\max_j D_j(t)$')
        ax.set_xlim(-2.5, -.96)
        ax.legend(frameon=False, fontsize=8)
    for ax in axes.flat:
        ax.set_xlabel(r'$t$')
        ax.axvline(float(data['t_star']), color='.4', linestyle=':', linewidth=.9)
        ax.axvline(float(data['peak']), color='.4', linestyle='-.', linewidth=.9)
    image_path = ROOT/'results/rigid_stokes_comparison.png'
    fig.savefig(image_path, dpi=200)
    fig.savefig(image_path.with_suffix('.pdf'))
    plt.close(fig)

    s = matrix(initial['s'])
    stokes = '\n'.join(f'| {j} | {complex_number(s[j], 12)} | ' +
                       ' | '.join(complex_number(j0[j, k], 10) for k in range(2)) + ' |' for j in range(4))
    condition_table = '\n'.join(f'| {t:.9f} | {large:.3e} | {small:.3e} | {cond:.3e} |'
                                for t, large, small, cond in conditions)
    ratios = ', '.join(f"{v['row_drift_ratio_RK_over_contour']:.2f}" for v in data['pairs'].values())
    cost_ratios = ', '.join(f"{v['time_ratio_contour_over_RK']:.1f}" for v in data['pairs'].values())
    report = r'''# Вариации данных Стокса при жёсткой потере устойчивости: численный опыт

## Фон и линеаризация

Рассматривается уравнение из препринта О. М. Киселёва (1999)

\[
\varepsilon^2 u_{tt}+2u^3+tu=1,\qquad \varepsilon=0.2,\quad -7\le t\le-1.
\]

Введём p=epsilon u_t и вариацию Y=(v,epsilon v_t)^T. При фиксированном
epsilon матрица перехода F удовлетворяет

\[
F_t=M(t)F,\quad F(-7)=I,\qquad
M(t)=\varepsilon^{-1}\begin{pmatrix}0&1\\-(6u^2+t)&0\end{pmatrix}.
\]

Начальные условия фона заданы двухчленным приближением к нижнему корню
2r^3+tr=1: u=r+epsilon^2 b, p=epsilon(r'+epsilon^2 b'),
b=12r^3/(6r^2+t)^4-2r/(6r^2+t)^3, при t=-7.
Это конкретная задача Коши, приближающая асимптотический фон препринта.
Точка слияния корней t_*=-3*2^(-1/3)=-2.381101578;
первый максимум u имеет координату **PEAK**.

Данные Стокса вычисляются в шести точках: -7, t_*, t_peak-0.1,
t_peak, t_peak+0.2, -1. Все оценки максимума ошибки и дрейфа ниже
относятся к этим точкам, а не к доказанной равномерной оценке на интервале.

## Вычисление данных Стокса

Используется переход к q_xx=2q^3+xq+alpha:

\[
x=-t\varepsilon^{-2/3},\quad q=i\varepsilon^{-1/3}u,\quad
w=q_x=-i\varepsilon^{-2/3}p,\quad \alpha=i/\varepsilon=5i.
\]

Спектральная система Psi_lambda=A Psi имеет матрицу

\[
A=-i(4\lambda^2+x+2q^2)\sigma_3+
(4q\lambda-\alpha/\lambda)\sigma_1-2w\sigma_2,
\]

где sigma_1,sigma_2,sigma_3 — матрицы Паули. Совместная система
Psi_x=B Psi имеет B=-i lambda sigma_3+q sigma_1.
Канонический столбец z_j, j=0,...,5, нормирован главным коэффициентом e_1
при чётном j и e_2 при нечётном j; его экспонента есть
exp[-(-1)^j i(4lambda^3/3+x lambda)].
Начальное асимптотическое направление
phi_j=-pi/6+j pi/3 находится в центре соответствующего сектора убывания.

Каждый столбец независимо продолжается от R exp(i phi_j) по лучу до
1.5 exp(i phi_j), затем по хордам окружности радиуса 1.5 к lambda_*=1.5.
Угловой шаг хорды не превышает pi/6. Угол изменяется непрерывно от phi_j
до нуля: для j=5 это продолжение от 3pi/2 до 0, без замены на -pi/2.
Так фиксируется один согласованный подъём путей на логарифмическое
накрытие проколотой плоскости. Все пути обходят регулярную особую точку
lambda=0; локальные степени равны lambda^(+-alpha).

Положим [a,b]=a_1 b_2-a_2 b_1. Вычисляются четыре коэффициента связи

\[
z_{j+2}=a_j z_j+s_j z_{j+1},\qquad
s_j=\frac{[z_j,z_{j+2}]}{[z_j,z_{j+1}]},\quad j=0,1,2,3.
\]

Индексы относятся к приведённым направлениям; это избыточный набор
данных Стокса, а не четыре независимых комплексных параметра.
Определители соседних столбцов вычисляются, без принудительной нормировки.
Их отклонение от (-1)^j служит дополнительным контролем.

Начальные значения (округлены; мнимые части на уровне численной ошибки опущены):

| j | s_j(-7) | partial_u s_j(-7) | partial_p s_j(-7) |
| --- | --- | --- | --- |
STOKES_TABLE

## Сохраняемая величина для линеаризованного уравнения

Обозначим J_j(t)=(partial_u s_j,partial_p s_j), J — матрицу из этих строк.
Производные вычисляются при фиксированных t и epsilon. Для них решаются
спектральные системы чувствительности

\[
(z_q)_\lambda=A z_q+A_q z,\qquad
(z_w)_\lambda=A z_w+A_w z.
\]

Начальные производные асимптотических рядов вычисляются центральной
разностью в арифметике повышенной точности (100 десятичных разрядов,
шаг 10^(-34)). Затем дифференцируется приведённое отношение определителей
и применяется переход (q,w) к (u,p).

Сохранение s_j вдоль нелинейного решения означает

\[
\partial_t s_j+\frac{p}{\varepsilon}\partial_u s_j+
\frac{1-2u^3-tu}{\varepsilon}\partial_p s_j=0.
\]

Дифференцирование по начальным условиям даёт точное равенство

\[
\delta s=J(t)Y(t),\qquad J(t)F(t)=J(-7),\qquad
\frac{d}{dt}\delta s=0.
\]

Именно это равенство проверяется численно. Строки J(t) в каждой точке
получены новым спектральным расчётом; из F или из условия сохранения
они не восстанавливались. Параметр alpha не варьируется; постоянство
собственных значений локальной монодромии само по себе этой проверки
не заменяет.

## Контурное решение и сравнение

Интегрируются ядра K=z_1^2+z_2^2 и
K_x=-2i lambda(z_1^2-z_2^2)+4q z_1 z_2.
Используются два взвешенных контура из лучевых ветвей с номерами
(0,1,2,3) и (2,3,4,5). Коэффициенты их линейных комбинаций определены
один раз при t=-7 условием сокращения трёх компонент симметрического
квадрата столбцов в точке lambda_*.
Каждый контур использует разные секторы убывания при бесконечности.
Нулевые граничные слагаемые обеспечиваются этим сопряжением и убыванием
R=-i(z_1^2-z_2^2)/2 вдоль указанных направлений.

Нормировка столбцов при изменении t переносится системой B при lambda_*=1.5.
В физических переменных её матрица
i lambda_* epsilon^(-2/3) sigma_3-i u epsilon^(-1) sigma_1
косоэрмитова. Этот перенос использует только нелинейный фон.
Вторая компонента каждого нормированного столбца независимо контролируется.
Полученная контурная матрица Phi нормируется один раз: F_C(t)=Phi(t)Phi(-7)^(-1).
Её k-й столбец равен сумме по четырём ветвям соответствующего контура
с фиксированными коэффициентами c_j:

\[
\Phi_k(t)=\sum_j c_j\begin{pmatrix}
-i\varepsilon^{1/3}\int_{\gamma_j}K_j\,d\lambda\\
i\varepsilon^{2/3}\int_{\gamma_j}(K_j)_x\,d\lambda
\end{pmatrix},
\]

где gamma_j направлена от бесконечности к lambda_*.
Монодромия и вронскиан при этом не проектируются на заданные значения.

В обоих методах используется один и тот же высокоточный нелинейный фон
и арифметика с 90 десятичными разрядами. Прямой метод — адаптивная пара
Dormand–Prince 5(4); контурный — спектральное продолжение и квадратуры
на основе рядов Тейлора порядка 40. Контролируются хвосты рядов как
столбцов, так и интегралов. Допуски этих двух алгоритмов имеют разный
смысл; сравнение проводится при близких фактических ошибках F.

Пусть ||C||_max=max_ab |C_ab|. В таблице приведены

\[
E=\max_{t\in T}\frac{\|F_{num}(t)-F_{ref}(t)\|_{max}}{\|F_{ref}(t)\|_{max}},
\qquad D=\max_j\max_{t\in T}
\frac{\|J_j(t)F_{num}(t)-J_j(-7)\|_{max}}{\|J_j(-7)\|_{max}},
\]

где T — шесть перечисленных точек. Построчная нормировка необходима:
масштабы строк J различаются примерно на двадцать порядков.
Время включает подготовку контуров и нормировочный перенос; общий фон
и независимый монитор в стоимость каждого метода не включены.

Дополнительно W_err=max_{t in T}|det F_num(t)-1| контролирует вронскиан.

| Метод | Внутренний допуск | E | D | W_err | Время, с |
| --- | --- | --- | --- | --- | --- |
COMPARISON_TABLE

Максимальные дрейфы отдельных строк:

| Метод, допуск | D_0 | D_1 | D_2 | D_3 |
| --- | --- | --- | --- | --- |
DETAILS_TABLE

Для обычного выбора допуска Рунге–Кутты 10^(-12) получено E=BASE_E,
D=BASE_D. При согласованных ошибках решения контурный дрейф меньше
в RATIO раза для двух уровней точности соответственно; затраты времени
больше в COST_RATIO раза. Различаются также порядки методов.

![Фон, усиление и дрейф вариаций Стокса](results/rigid_stokes_comparison.png)

На верхних панелях показаны фон и усиление матрицы F, F(-7)=I.
На нижних — дрейф в пяти неначальных контрольных точках; соединительные
линии служат для чтения рисунка. Вертикальные пунктирная и
штрихпунктирная линии обозначают t_* и t_peak.

## Обусловленность

Для действительных вариаций (u,p) рассмотрим вещественную матрицу
с восемью строками, составленную из действительных и мнимых частей
J_j(t)/||J_j(-7)||_max. Её сингулярные числа характеризуют чувствительность
этого нормированного отображения к возмущениям состояния.

| t | sigma_max | sigma_min | sigma_max/sigma_min |
| --- | --- | --- | --- |
CONDITION_TABLE

Это характеристика выбранных переменных и нормировки. Рост F во время
выброса совместим с постоянством delta s: точное равенство
J(t)=J(-7)F(t)^(-1) описывает изменение чувствительности монодромных
координат. Оно использовано для интерпретации, а не для вычисления J.
На максимуме выброса число обусловленности этого отображения достигает
около 1.3e3, при начальном значении около 4.1.

## Независимый контроль

Основной спектральный монитор: 100 разрядов, R=8, 80 членов
асимптотического ряда, порядок Тейлора 40, допуск 10^(-32).
В начальной точке и на максимуме выполнено уточнение: 120 разрядов,
R=10, 112 членов, порядок 44, допуск 10^(-42).
Фон и опорная матрица F вычислены локальными рядами Тейлора
с 90 разрядами и допуском 10^(-36), с независимым повторением при
65 разрядах и допуске 10^(-27).

| Проверка | Максимальное отклонение |
| --- | --- |
CHECKS_TABLE

Уточнение спектрального расчёта согласуется с уровнем остаточного дрейфа
на опорном решении. Этот уровень существенно ниже измеренных ошибок
обоих методов. Все числа являются результатами численной сходимости,
не интервальными гарантированными оценками.

## Итог и воспроизведение

На выбранном фоне жёсткой потери устойчивости непосредственно вычислены
данные Стокса и их ненулевые вариации. Контурный метод даёт меньший дрейф
при сопоставимой ошибке решения и большей стоимости. Опыт относится
к epsilon=0.2 и первому выбросу; зависимость дрейфа от epsilon и длинная
последовательность последующих колебаний этим расчётом не установлены.

Данные и снимки расчётных модулей: `results/rigid_stokes_e02/`.
Для нового расчёта требуется новое имя выходной папки:

```sh
python computational_preprint/compare_rigid_monodromy.py --output NEW_DIRECTORY
python -m unittest discover -s computational_preprint -p 'test_*.py' -v
python computational_preprint/build_rigid_stokes_report.py
```

Зависимости высокоточной среды указаны в requirements-high-precision.txt.
Полный набор из 35 тестов пройден, включая символьные проверки замены
переменных и спектральных тождеств, а также численные проверки
асимптотических коэффициентов, спектральных чувствительностей и переноса.
Хеши исходных статей, предыдущих результатов и журнальных архивов
проверены после расчёта: защищённые файлы не изменены.
'''
    replacements = {
        'PEAK': f"t_peak={float(data['peak']):.12f}", 'STOKES_TABLE': stokes,
        'COMPARISON_TABLE': '\n'.join(comparison), 'DETAILS_TABLE': '\n'.join(details),
        'BASE_E': number(baseline['max_solution_error']),
        'BASE_D': number(baseline['max_row_variation_drift']),
        'COST_RATIO': cost_ratios, 'RATIO': ratios, 'CONDITION_TABLE': condition_table,
        'CHECKS_TABLE': '\n'.join(f'| {name} | {number(value)} |' for name, value in checks.items()),
    }
    for key, value in replacements.items():
        report = report.replace(key, value)
    (ROOT/'RIGID_STOKES_RU.md').write_text(report)
    print(json.dumps({'pairs': data['pairs'], 'monitor_floor': floor,
                      'conditioning': conditions, 'checks': {k:float(v) for k,v in checks.items()}}, indent=2))


if __name__ == '__main__':
    main()
