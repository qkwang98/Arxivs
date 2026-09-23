#!/usr/bin/env python3
"""Build the paired report and monochrome pointwise diagnostics from saved runs."""
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


ROOT = Path(__file__).parent


def scientific(value):
    return f'{value:.3e}'


def main():
    bundles = []
    for directory in ('equal_accuracy_coarse_matched','equal_accuracy_fine'):
        data = json.loads((ROOT/'results'/directory/'results.json').read_text())
        name,pair = next(iter(data['pairs'].items()))
        if not pair['matched']:
            raise RuntimeError('Unmatched pair in '+directory)
        bundles.append((directory,data,data['contours'][name],data['rk_trials'][pair['rk_tolerance']],pair))
    table = ['| Уровень | Метод | Максимальная ошибка E | Максимальный дрейф D | Дрейф вронскиана | Время, с |',
             '|---|---|---:|---:|---:|---:|']
    ratios,local,settings = [],[],[]
    for index,(directory,data,contour,rk,pair) in enumerate(bundles,1):
        table.append(f'| {index} | Контуры | {scientific(contour["max_solution_error"])} | {scientific(contour["max_variation_drift"])} | {scientific(contour["max_wronskian_error"])} | {contour["standalone_seconds"]:.2f} |')
        table.append(f'| {index} | RK45 MP | {scientific(rk["max_solution_error"])} | {scientific(rk["max_variation_drift"])} | {scientific(rk["max_wronskian_error"])} | {rk["seconds"]:.2f} |')
        ratios.append(f'На уровне {index} отношение ошибок RK/контуры равно {pair["rk_to_contour_error_ratio"]:.3f}; '
                      f'отношение дрейфов RK/контуры равно {pair["rk_to_contour_drift_ratio"]:.2f}; '
                      f'отношение затрат контуры/RK равно {pair["contour_to_rk_cost_ratio"]:.2f}.')
        cr = next(row for row in contour['points'] if row['t'] == .62)
        rr = next(row for row in rk['points'] if row['t'] == .62)
        local.append(f'| {index} | Контуры | {scientific(cr["solution_error"])} | {scientific(cr["variation_drift"])} |')
        local.append(f'| {index} | RK45 MP | {scientific(rr["solution_error"])} | {scientific(rr["variation_drift"])} |')
        settings.append(f'- Уровень {index}: R={contour["radius"]:g}, порядок формального ряда {contour["formal_order"]}, '
                        f'спектральный допуск {contour["spectral_tolerance"]}; '
                        f'допуск RK45 MP {rk["tolerance"]}, шагов {rk["accepted_steps"]}, отклонённых {rk["rejected_steps"]}.')
    lines = [
        '# Сравнение при общей арифметике и согласованной ошибке решения',
        '', '## Условия', '',
        'Оба алгоритма выполнены в 70-значной арифметике mpmath/gmpy2 на одном высокоточном фоне. '
        'Отрезок: x=0.23+0.07i+t, -6 <= t <= 6. Начальная фундаментальная матрица F(0)=I. '
        'Контрольные точки: t=-6,-3,0,0.62,3,6.', '',
        'F переводит начальные значения (y,y\') в значения в текущей точке. '
        'E есть максимум поточечной относительной нормы F_num-F_ref; в каждой точке '
        'нормирование производится на максимальный модуль элемента F_ref именно в этой точке. '
        'D есть максимум нормы J(t)F_num(t)-J(0), нормированной на максимальный модуль элемента J(0). '
        'В обеих формулах максимум берётся по указанным шести точкам.', '',
        'J есть независимо вычисленный спектральный якобиан произведений '
        's1*s2, s2*s3, s3*s4, s1*s4 по координатам (y,y\'). Эти четыре величины избыточны. '
        'Монодромный контроль общий для обоих методов; он не участвует в подборе допусков.', '',
        'Для контурного решения используется согласование нормировки через B-систему в конечных '
        'точках lambda=+1.45 и -1.45. RK45 MP реализует пару Дормана–Принса 5(4) с точными '
        'рациональными коэффициентами и контролем среднеквадратичной нормированной локальной ошибки. '
        'Все стадии вычисляются в многократной арифметике. Контрольные точки достигаются шагами; '
        'полином интерполяции меньшего порядка не используется.', '',
        'Коэффициенты сверены с [SciPy RK45](https://docs.scipy.org/doc/scipy/reference/generated/scipy.integrate.RK45.html). '
        'Проверены один шаг, сходимость на известном решении в обоих направлениях и согласование '
        'с локальным высокоточным решением П4. Это отдельная реализация RK45 MP, а не вызов float64 solve_ivp.', '',
        '## Подбор точности', '',
        'Допуск RK подбирался только по E. Пара принималась, когда отношение E_RK/E_contour '
        'лежало между 1/1.1 и 1.1. Решения не масштабировались и не проецировались на известные '
        'инварианты после расчёта. Все пробные допуски и их результаты сохранены.', '',
        *settings, '', '## Результат', '', *table, '', *ratios, '',
        'В обеих согласованных парах стабилизированная контурная реализация даёт меньший '
        'максимальный дрейф вариаций монодромии. Общая арифметика и близкие значения E '
        'позволяют отделить этот наблюдаемый эффект от прежнего сравнения 70-значных '
        'контурных расчётов с float64 RK45. При этом RK45 MP быстрее и лучше сохраняет '
        'вронскиан. Общего превосходства одного алгоритма по всем критериям здесь нет.', '',
        '## Распределение ошибки', '',
        'Отдельно контролируется вронскиан: максимальное значение |det F_num-1|. '
        'Этот показатель сохранён в таблице наряду с монодромным дрейфом, '
        'поскольку выигрыш по одному из критериев не означает выигрыша по всем интегралам сохранения.', '',
        'Равенство максимумов E не означает равенства ошибок в каждой точке. '
        'Например, около области быстрого роста, при t=0.62:', '',
        '| Уровень | Метод | Поточечная ошибка | Поточечный дрейф |',
        '|---|---|---:|---:|', *local, '',
        'Поэтому различие D следует интерпретировать как результат всей стабилизированной '
        'контурной реализации и её распределения погрешности по отрезку. '
        'Оно не доказывает универсального преимущества интегральных представлений при одинаковой '
        'локальной ошибке. Для точного якобиана ошибка вариации имеет вид J(t)E_F(t); '
        'существенны и величина, и направление матричной ошибки E_F.', '',
        f'![Поточечные ошибки и дрейф]({(ROOT/"results/equal_accuracy_comparison.png").resolve()})', '',
        'На рисунке показаны только вычисленные точки, без интерполяции между ними. '
        'Начальная точка с заданной нормировкой исключена из логарифмических графиков.', '',
        '## Учёт затрат', '',
        'Время контурного метода включает подготовку обеих нормировочных B-систем, '
        'вычисление начального базиса, спектральные решения и интегралы во всех шести точках. '
        'Даже при повторном использовании B-систем в серии их полная стоимость включена '
        'в стоимость каждого самостоятельного контурного расчёта.', '',
        'Общая подготовка фона и опорного решения и ранее вычисленный общий якобиан J '
        'исключены из затрат обоих методов. Время подбора допусков не включено в время '
        'выбранного RK-расчёта; все попытки и полная продолжительность серий сохранены. '
        'Для уточнённого согласования использованы сохранённые контурные значения '
        'с проверкой совпадения фона и опорного решения. Их время перенесено из исходного запуска. '
        'Замеры однократны, не являются статистическим тестом быстродействия.', '',
        '## Границы вывода', '',
        'Это первый сопоставимый опыт на одном фоне, двух уровнях E и шести контрольных точках. '
        'Он относится к данной реализации контурной формулы и RK45 MP, а не ко всему классу '
        'методов Рунге–Кутты. Сравнение не является строгой оценкой ошибок на непрерывном отрезке. '
        'Опорный расчёт и спектральный контроль предварительно проверены уточнением '
        'в STABILIZATION_RU.md; их расхождения существенно меньше исследуемых здесь ошибок.', '',
        '## Воспроизводимость', '',
        'Исходные результаты: results/equal_accuracy/results.json. Снимок первоначальной '
        'версии программы сохранён рядом в runner_snapshot.py. Два окончательно согласованных '
        'уровня: results/equal_accuracy_coarse_matched/results.json и results/equal_accuracy_fine/results.json. '
        'В JSON сохранены высокоточные матрицы, все попытки подбора, версии арифметики и хеши кода. '
        'Файлы отправленной статьи и прежний каталог verification не изменены.', '',
        'Команды запуска в окружении из requirements-high-precision.txt:', '',
        '```sh',
        'python computational_preprint/compare_equal_accuracy.py --radii 14 --spectral-tolerance 1e-23 --match-factor 1.1 --reuse-contours computational_preprint/results/equal_accuracy_coarse/results.json --reuse-rk-trials --output computational_preprint/results/coarse_repeat',
        'python computational_preprint/compare_equal_accuracy.py --radii 14 --spectral-tolerance 1e-26 --match-factor 1.1 --reuse-contours computational_preprint/results/equal_accuracy/results.json --reuse-rk-trials --output computational_preprint/results/fine_repeat',
        'python computational_preprint/build_equal_accuracy_report.py',
        '```', '',
        'Новые расчёты записываются в новые каталоги. Генератор этого отчёта читает '
        'окончательные каталоги equal_accuracy_coarse_matched и equal_accuracy_fine.', '']
    (ROOT/'EQUAL_ACCURACY_RU.md').write_text('\n'.join(lines))
    fig,axes = plt.subplots(2,2,figsize=(10,7),layout='constrained')
    for row,(_,data,contour,rk,pair) in enumerate(bundles):
        for col,(key,label) in enumerate((('solution_error','Pointwise relative error'),('variation_drift','Monodromy-variation drift'))):
            ax = axes[row,col]
            for result,marker,face,name in ((contour,'o','white','Contour'),(rk,'s','black','RK45 MP')):
                records = [v for v in result['points'] if v['t'] != 0]
                ax.semilogy([v['t'] for v in records],[v[key] for v in records],linestyle='none',marker=marker,
                            markersize=6,markerfacecolor=face,markeredgecolor='black',label=name)
            ax.set_title(f'Level {row+1}: {label}',fontsize=11)
            ax.set_xlabel('t,  x = 0.23 + 0.07i + t')
            ax.set_xticks([-6,-3,0,3,6])
            ax.grid(True,which='major',color='.85',linewidth=.5)
            if row == 0 and col == 0:
                ax.legend(fontsize=9)
    fig.savefig(ROOT/'results/equal_accuracy_comparison.png',dpi=180)
    plt.close(fig)
    print('Report and monochrome figure generated')


if __name__ == '__main__':
    main()
