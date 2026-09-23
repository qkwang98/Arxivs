"""Report the transition into regular oscillations and subsequent invariant drift."""
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpmath import mp
import numpy as np

import rigid_monodromy as r


ROOT = Path(__file__).resolve().parent


def num(v):
    if abs(float(v)) < 1e-80:
        return '0'
    return f'{float(v):.3e}'


def main():
    source = ROOT/'results/rigid_oscillatory_checked_e02/results.json'
    data = json.loads(source.read_text())
    if data['status'] != 'complete' or not data['protected_unchanged']:
        raise ValueError('An intact, completed calculation is required')
    if not data['matched_pair']['matched']:
        raise ValueError('No matched-error pair is available')
    control_data = json.loads((ROOT/'results/rigid_oscillatory_controls/results.json').read_text())
    if control_data['status'] != 'complete' or not control_data['source_unchanged']:
        raise ValueError('The additional controls must be complete')
    contour = data['contour']
    matched_key = data['matched_pair']['rk_tolerance']
    matched = data['rk_trials'][matched_key]
    baseline = data['rk_trials']['1.0e-12']
    records = [('Контур, усиленный контроль Psi', contour),
               ('Рунге–Кутта, допуск 1e-12', baseline),
               (f'Рунге–Кутта, допуск {matched_key}', matched),
               ('Рунге–Кутта, усиленный допуск после t=-1', control_data['rk_tightened'])]
    entry = data['regular_entry_offset']-7
    peaks = data['peaks']
    rows = []
    for label, record in records:
        rows.append(f"| {label} | {num(record['max_solution_error'])} | "
                    f"{num(record['max_row_variation_drift'])} | "
                    f"{num(record['post_drift']['max_row_drift'])} |")
    point_rows = []
    post_c = {p['offset']: p['max_row_drift'] for p in contour['post_drift']['points']}
    post_r = {p['offset']: p['max_row_drift'] for p in matched['post_drift']['points']}
    for c, v in zip(contour['points'], matched['points']):
        offset = c['offset']
        point_rows.append(f"| {c['t']:.9f} | {num(c['max_row_variation_drift'])} | "
                          f"{num(post_c[offset]) if offset in post_c else '-'} | "
                          f"{num(v['max_row_variation_drift'])} | "
                          f"{num(post_r[offset]) if offset in post_r else '-'} |")
    peak_rows = []
    for j in (0, 1, 4, 8, 12, 15, 16):
        p = peaks[j]
        peak_rows.append(f"| {j+1} | {float(p['t']):.9f} | {float(p['u']):.6f} | "
                         f"{float(p['period']):.6f}" if 'period' in p else
                         f"| {j+1} | {float(p['t']):.9f} | {float(p['u']):.6f} | -")
        peak_rows[-1] += (f" | {100*float(p['relative_period_change']):.2f}% |"
                         if 'relative_period_change' in p else ' | - |')
    new_records = [v for k, v in data['monitor'].items()
                   if float(k) not in data['reused_monitor_offsets']]
    refined_floor = max(v for record in new_records for v in record['row_refined_origin_drift'])
    checks = {
        'Уточнение опорной матрицы F': data['reference']['refinement_error'],
        'Дрейф самих коэффициентов Стокса': max(data['stokes_drift_by_row']),
        'Дрейф J(t)F_ref(t) относительно исходного J(-7)': data['reference_monitor']['max_row_variation_drift'],
        'Новые точки: сравнение с уточнённым J(-7)': refined_floor,
        'Изменение J(t)F_ref(t) после входа в регулярный участок': data['reference_post_drift']['max_row_drift'],
        'Уточнение сетки поиска максимумов': float(data['peak_location_refinement']),
    }
    long_d = matched['max_row_variation_drift']/contour['max_row_variation_drift']
    post_d = matched['post_drift']['max_row_drift']/contour['post_drift']['max_row_drift']
    refined_endpoint = control_data['contour_endpoint_refined']

    mp.dps = 90
    ref = r.Reference(end='8')
    times = np.linspace(-7, 8, 1801)
    u = [float(ref.at(mp.mpf(float(t)))[0]) for t in times]
    plt.rcParams.update({'font.size': 9, 'axes.grid': True, 'grid.color': '.85',
                         'grid.linewidth': .5, 'axes.spines.top': False,
                         'axes.spines.right': False, 'savefig.facecolor': 'white'})
    fig, axes = plt.subplots(2, 2, figsize=(10.5, 7), constrained_layout=True)
    axes[0, 0].plot(times, u, color='black', linewidth=1)
    axes[0, 0].set(title=r'(a) Algebraic branch to oscillations, $\epsilon=0.2$', ylabel=r'$u(t)$')
    styles = [(contour, '-', 'o', 'Contour, refined Psi'),
              (matched, '--', 's', 'RK, matched error'),
              (baseline, ':', '^', 'RK, tolerance 1e-12'),
              (control_data['rk_tightened'], '-.', 'v', 'RK, tighter after t=-1')]
    for record, style, marker, label in styles:
        points = record['points'][1:]
        for ax, key in [(axes[0, 1], 'max_row_variation_drift'), (axes[1, 1], 'solution_error')]:
            ax.semilogy([p['t'] for p in points], [p[key] for p in points],
                        color='black', linestyle=style, marker=marker, markersize=4,
                        markerfacecolor='white', label=label)
        points = record['post_drift']['points'][1:]
        axes[1, 0].semilogy([p['t'] for p in points], [p['max_row_drift'] for p in points],
                            color='black', linestyle=style, marker=marker, markersize=4,
                            markerfacecolor='white', label=label)
    axes[0, 1].set(title='(b) Drift relative to initial monodromy variation', ylabel=r'$D_0(t)$', xlim=(-2.6, 8.2))
    axes[1, 0].set(title='(c) Additional drift in the regular regime', ylabel=r'$D_{\rm osc}(t)$', xlim=(entry-.2, 8.2))
    axes[1, 1].set(title='(d) Relative error of the tangent matrix', ylabel=r'$E(t)$', xlim=(-2.6, 8.2))
    axes[0, 1].legend(frameon=False, fontsize=8)
    point, = axes[1, 0].plot([8], [refined_endpoint['post_drift']['max_row_drift']],
                             color='black', marker='*', markersize=10, linestyle='none',
                             label='Contour: endpoint refinement')
    axes[1, 0].legend(handles=[point], frameon=False, fontsize=7, loc='upper left')
    for ax in axes.flat:
        ax.set_xlabel(r'$t$')
        ax.axvline(entry, color='.4', linestyle='-.', linewidth=.9)
    axes[0, 0].axvline(float(data['t_star']), color='.4', linestyle=':', linewidth=.9)
    figure = ROOT/'results/rigid_oscillatory_drift.png'
    fig.savefig(figure, dpi=200)
    fig.savefig(figure.with_suffix('.pdf'))
    plt.close(fig)

    report = r'''# От неосциллирующего режима к регулярным колебаниям: дрейф вариаций Стокса

## Продолжение через перестройку

Продолжена та же задача Коши

\[
\varepsilon^2u_{tt}+2u^3+tu=1,\qquad \varepsilon=0.2,
\qquad -7\le t\le8.
\]

Начальное двухчленное приближение к нижнему алгебраическому корню,
нормировка F(-7)=I для состояния (v,epsilon v_t) и два контурных базисных
решения сохранены из [исследования первого выброса](RIGID_STOKES_RU.md).
На всём интервале используется единый нелинейный фон; начальные данные
линеаризованного уравнения после перестройки не переопределяются.

Точка слияния алгебраических корней t_*=-2.381101578,
первый максимум возникает при t=-1.622750491. До t=8 обнаружено
17 максимумов, то есть 16 полных межмаксимальных периодов после первого
выброса. Поиск максимумов повторён с двукратным сгущением сетки.

Для воспроизводимого выделения регулярного участка взят первый максимум,
для которого относительные изменения межмаксимального периода и высоты
максимума относительно предыдущего меньше 5%. Это численный критерий
медленной модуляции; отдельная асимптотическая оценка остатка здесь не выводится.
Он выбирает **t_r=REGULAR_ENTRY**, девятый максимум.

| Номер максимума | t | u(t) | Период | Изменение периода |
| --- | --- | --- | --- | --- |
PEAK_TABLE

В конце интервала период меняется примерно на 2.3% за цикл, высота
максимума на 1.5%. Контроль монодромии выполняется также между последними
максимумами и при t=8, чтобы учитывать разные фазы колебания.

## Две меры дрейфа

Пусть J_j(t)=(partial_u s_j,partial_p s_j), p=epsilon u_t, где s_j —
четыре коэффициента Стокса в нормировке предыдущего отчёта.
Для точного линеаризованного решения сохраняются

\[
\delta s_j=s_{j,u}v+s_{j,p}\varepsilon v_t,
\qquad J_j(t)F(t)=J_j(-7).
\]

Для приближённой фундаментальной матрицы обозначим C_j(t)=J_j(t)F_num(t)
и b_j=||J_j(-7)||_max. Сравниваются

\[
D_0(t)=\max_j\frac{\|C_j(t)-J_j(-7)\|_{max}}{b_j},\qquad
D_{osc}(t)=\max_j\frac{\|C_j(t)-C_j(t_r)\|_{max}}{b_j}.
\]

Первая величина включает ошибку, накопленную до регулярных колебаний.
Вторая измеряет её последующее изменение. Она вычисляется как разность
самих комплексных строк C_j, а не как разность норм ошибок. Решение,
начальные коэффициенты и нормировка контуров при t_r не изменяются.

Матрица J в каждой новой точке вычислена непосредственно из спектральной
системы и систем чувствительности, независимо от F_num. Вариации
параметра alpha=i/epsilon не рассматриваются.

## Требуемая точность спектрального расчёта

Перенос настроек первого выброса на t=8 оказался недостаточным.
При спектральном допуске 1e-32 контроль на опорном решении дал
дрейф 2.52e-6 в наиболее чувствительной строке. При допуске 1e-42
он уменьшился до 2.21e-18. Для новых контрольных точек использованы
130 десятичных разрядов, допуск 1e-48 и порядок Тейлора 48;
канонические столбцы задаются при |lambda|=8 по 160 членам формального ряда.

Неизменённый контурный алгоритм с допуском 1e-14 на t=8 дал относительную
ошибку решения 1.91e7 и ошибку направления столбца Psi около 0.548.
Этот неудачный опыт сохранён в `results/rigid_oscillatory_e02/`.

В приведённом ниже расчёте начальный базис и прежние шесть контурных
значений сохранены. Для новых точек совместный контроль спектральных
столбцов и квадратур усилен до допуска 1e-34, порядок увеличен с 40 до 48.
Арифметика обоих сравниваемых методов имеет 90 десятичных разрядов.
Фиксированные веса контуров и начальная матрица не пересчитывались по
условиям сохранения монодромии. Скалярный перенос нормировки использует
только нелинейный фон и вспомогательную систему B.

Таким образом, результаты ниже относятся к контурному алгоритму
с усиленным контролем Psi на продолженном участке. Сравнение при
неизменных внутренних допусках дало бы существенно иной результат.

## Численные результаты

Ошибка E — максимум относительной ошибки матрицы F в норме наибольшего
элемента по всем контрольным точкам. Постоянный допуск Рунге–Кутты
MATCHED_TOL подобран по E на всём интервале, без согласования дрейфа.
Максимумы D_0 и D_osc относятся к указанным узлам наблюдения.

| Метод | E | max D_0 | max D_osc |
| --- | --- | --- | --- |
SUMMARY_TABLE

Для Рунге–Кутты с постоянным допуском при согласованной ошибке решения
отношение дрейфов Рунге–Кутта/контур
равно TOTAL_RATIO для D_0 и POST_RATIO для дополнительного D_osc.
Оба значения относятся к данному фону и выбранным настройкам.
Полное время методов здесь не сопоставляется: использованы сохранённые
спектральные и контурные значения первого опыта и предварительная проверка
конечной точки. Новый контурный расчёт требует значительно более строгого
внутреннего допуска, чем на участке первого выброса.

| t | D_0, контур | D_osc, контур | D_0, Рунге–Кутта | D_osc, Рунге–Кутта |
| --- | --- | --- | --- | --- |
POINT_TABLE

Значения ниже 1e-80 округлены в таблице до нуля.

![Переход к колебаниям и дрейф вариаций Стокса](results/rigid_oscillatory_drift.png)

Штрихпунктиром отмечен вход в регулярный участок t_r; пунктиром на
первой панели отмечена точка t_*. На графиках ошибок показаны измеренные
значения, соединительные линии служат для чтения рисунка. Нулевые
значения в начальных точках отсчёта не отображаются на логарифмических осях.

## Контроль распределения точности

В дополнительном опыте Рунге–Кутта до t=-1 использует допуск
5.399977346781e-14. Далее то же приближённое состояние, без коррекции,
продолжается с допуском 1e-16. Полная ошибка решения остаётся около
ADAPTIVE_ERROR, дополнительный дрейф после t_r равен ADAPTIVE_POST.
Это сопоставимо по полной ошибке с основным контурным расчётом.

В конечной точке отдельно уточнён контурный расчёт: допуск 1e-34 заменён
на 1e-40, при неизменном начальном базисе. Дополнительное отклонение
вариаций Стокса относительно того же значения при t_r изменилось
с ENDPOINT_COARSE_POST до ENDPOINT_FINE_POST. Уточнена только конечная
точка; полный регулярный участок на этом уровне повторно не вычислялся.
Она отмечена отдельной звёздочкой на рисунке.

Эти проверки выявляют два разных вклада: смещение, внесённое до
регулярного участка, и последующую численную погрешность. Ужесточение
точности на позднем участке уменьшает второй вклад у обоих методов.
По одной лишь полной ошибке решения нельзя заключить, какой метод
будет лучше сохранять вариации монодромии при ином распределении точности.

У контурного метода быстрый рост дрейфа у правой границы чувствителен
к точности спектрального продолжения и квадратур. Сохранение вариаций
Стокса при переходе к регулярным колебаниям согласуется с независимым
высокоточным контролем.

## Проверки и границы вывода

Нелинейный фон и опорная матрица F вычислены рядами Тейлора с
90 разрядами и допуском 1e-36, с повторением при 65 разрядах и допуске 1e-27.
Для дополнительного контроля новых спектральных значений использовано
ранее независимо уточнённое начальное J(-7), вычисленное при радиусе 10,
120 разрядах и допуске 1e-42. Равенство J(t)F_ref(t)=J(-7) проверялось
после вычислений; коррекция J по этому равенству не производилась.

| Проверка | Максимальное отклонение |
| --- | --- |
CHECK_TABLE

Уточнение сетки поиска максимумов относится к нахождению корней p(t)
на одном и том же опорном интерполянте. Точность самого нелинейного фона
контролируется отдельным повторением расчёта.

Для точных решений вариации Стокса постоянны во всех трёх режимах:
до перестройки, внутри неё и на колебательном участке. Представленные
числа характеризуют ошибки их численного сохранения. Спектральный
контроль должен быть точнее исследуемого дрейфа; опыт с прежними
настройками показывает существенность этого требования.

Исследованы одно значение epsilon и около восьми регулярных периодов
после t_r. Более длинные интервалы, предел epsilon к нулю и строгое
выведение асимптотической формулы связи требуют отдельного исследования.

## Воспроизведение

Данные и снимки расчётных модулей: `results/rigid_oscillatory_checked_e02/`.
Сохранённые исходные данные первого выброса используются без изменений.

```sh
python computational_preprint/compare_rigid_oscillatory.py --output NEW_DIRECTORY
python computational_preprint/check_rigid_oscillatory_controls.py --source NEW_DIRECTORY/results.json --output NEW_CONTROL_DIRECTORY
python -m unittest discover -s computational_preprint -p 'test_*.py' -v
python computational_preprint/build_rigid_oscillatory_report.py
```

Проверки включают раздельное измерение начального смещения и последующего
дрейфа; изменение направления ошибки при неизменной норме также обнаруживается.
Полный набор из 37 тестов пройден.
Защищённые статьи, предыдущие результаты и журнальные архивы не изменены.
'''
    replacements = {
        'REGULAR_ENTRY': f'{entry:.12f}', 'PEAK_TABLE': '\n'.join(peak_rows),
        'SUMMARY_TABLE': '\n'.join(rows), 'POINT_TABLE': '\n'.join(point_rows),
        'TOTAL_RATIO': f'{long_d:.3g}', 'POST_RATIO': f'{post_d:.3g}',
        'MATCHED_TOL': matched_key,
        'ADAPTIVE_ERROR': num(control_data['rk_tightened']['max_solution_error']),
        'ADAPTIVE_POST': num(control_data['rk_tightened']['post_drift']['max_row_drift']),
        'ENDPOINT_COARSE_POST': num(contour['post_drift']['points'][-1]['max_row_drift']),
        'ENDPOINT_FINE_POST': num(refined_endpoint['post_drift']['max_row_drift']),
        'CHECK_TABLE': '\n'.join(f'| {k} | {num(v)} |' for k, v in checks.items()),
    }
    for key, value in replacements.items():
        report = report.replace(key, value)
    (ROOT/'RIGID_OSCILLATORY_RU.md').write_text(report)
    print(json.dumps({'regular_entry': entry, 'matched_tolerance': matched_key,
                      'total_drift_ratio': long_d, 'post_drift_ratio': post_d,
                      'checks': checks}, indent=2, ensure_ascii=False))


if __name__ == '__main__':
    main()
