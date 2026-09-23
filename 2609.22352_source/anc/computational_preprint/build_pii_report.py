#!/usr/bin/env python3
"""Build the PII pilot report and monochrome figures from saved results."""
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpmath import mp
import numpy as np

import pii_core as p


ROOT = Path(__file__).resolve().parent
DATA = ROOT/'results/pii_comparison/results.json'


def number(x):
    return f'{float(x):.3e}'


def matrix(raw):
    return mp.matrix([[mp.mpc(*v) if isinstance(v,list) else mp.mpf(v) for v in row] for row in raw])


def main():
    data = json.loads(DATA.read_text())
    if data.get('status') != 'complete' or not all(v['matched'] for v in data['pairs'].values()):
        raise ValueError('The report requires a completed matched comparison')
    if not data['protected_unchanged']:
        raise ValueError('Protected input files changed')
    mp.dps = 70
    levels = list(data['pairs'])
    plt.rcParams.update({'font.size':10, 'axes.spines.top':False, 'axes.spines.right':False,
                         'savefig.dpi':180})
    fig, axes = plt.subplots(2,len(levels),figsize=(12,6.3),layout='constrained')
    for k,tol in enumerate(levels):
        pair, contour = data['pairs'][tol],data['contours'][tol]
        runge = data['rk_trials'][pair['rk_tolerance']]
        for method,style,marker,label in ((contour,'-','o','Contour'),(runge,'--','x','RK45')):
            points = sorted([v for v in method['points'] if v['t'] != 0],key=lambda v:v['x'])
            for row,key in enumerate(('solution_error','variation_drift')):
                axes[row,k].semilogy([v['x'] for v in points],[v[key] for v in points],
                                     color='black',linestyle=style,marker=marker,
                                     markersize=4,markerfacecolor='white',label=label)
        axes[0,k].set_title(f'Level {k+1}: max E = {contour["max_solution_error"]:.1e}')
        for row in range(2):
            axes[row,k].set_xlabel('x')
            axes[row,k].set_xticks([-13,-10,-7,-4,-2])
            axes[row,k].grid(True,which='major',color='.85',linewidth=.5)
        axes[0,k].legend(frameon=False)
    axes[0,0].set_ylabel('Relative solution error E(x)')
    axes[1,0].set_ylabel('Monodromy variation drift D(x)')
    fig.savefig(ROOT/'results/pii_comparison.png')
    plt.close(fig)

    ref = p.Reference()
    xs = np.linspace(-13,-1,401)
    states = [ref.at(float(x+1)) for x in xs]
    fig, axes = plt.subplots(2,2,figsize=(10,7.4),layout='constrained')
    axes[0,0].plot(xs,[float(mp.re(s[0])) for s in states],color='black')
    axes[0,0].set(xlabel='x',ylabel='u(x)',title='PII background: u(-1)=0.2, u\'(−1)=0.1')
    fine = data['contours'][levels[-1]]
    for j,style,marker in ((0,'-','o'),(1,'--','s')):
        axes[1,0].plot(xs,[float(mp.re(s[3+2*j])) for s in states],color='black',linestyle=style,
                       label=f'v{j+1}: Taylor reference')
        points = sorted(fine['F'].items(),key=lambda v:float(v[0]))
        axes[1,0].plot([-1+float(t) for t,_ in points],
                       [float(mp.re(matrix(f)[0,j])) for _,f in points],linestyle='none',
                       marker=marker,markerfacecolor='white',color='black',markersize=5,
                       label=f'v{j+1}: contour')
    axes[1,0].set(xlabel='x',ylabel='v(x)',title='Normalized linearized solutions')
    axes[1,0].legend(frameon=False,fontsize=8,ncol=2)
    for row,group in enumerate(p.Contours.groups):
        ax = axes[row,1]
        for j in range(6):
            angle = -np.pi/6+j*np.pi/3
            edge = angle+np.pi/6
            ax.plot([0,np.cos(edge)],[0,np.sin(edge)],color='.75',linestyle=':',linewidth=.6)
            active = j in group
            end = np.array([np.cos(angle),np.sin(angle)])
            ax.plot([0,end[0]],[0,end[1]],color='black' if active else '.8',
                    linestyle='-' if j%2==0 else '--',linewidth=1.4 if active else .6)
            if active:
                ax.annotate('',xy=.4*end,xytext=.7*end,
                            arrowprops={'arrowstyle':'->','color':'black','lw':1})
            ax.text(*(1.13*end),f'$\\ell_{j}$',ha='center',va='center',color='black' if active else '.6')
        ax.text(.04,-.13,'0',fontsize=9)
        ax.set_aspect('equal')
        ax.set(xlim=(-1.3,1.3),ylim=(-1.28,1.28),xticks=[],yticks=[],
               title=f'Cycle {"A" if row==0 else "B"}: rays '+', '.join(map(str,group)))
        for spine in ax.spines.values():
            spine.set_visible(False)
    fig.savefig(ROOT/'results/pii_solutions_and_contours.png')
    plt.close(fig)

    rows, ratios = [], []
    for k,tol in enumerate(levels,1):
        pair = data['pairs'][tol]
        for name,record in (('Контур',data['contours'][tol]),('RK45',data['rk_trials'][pair['rk_tolerance']])):
            rows.append(f'| {k} | {name} | {number(record["max_solution_error"])} | '
                        f'{number(record["max_variation_drift"])} | {number(record["max_wronskian_error"])} | '
                        f'{record["seconds"]:.2f} |')
        ratios.append(f'| {k} | {pair["error_ratio_RK_over_contour"]:.4f} | '
                      f'{pair["drift_ratio_RK_over_contour"]:.3f} | {pair["cost_ratio_contour_over_RK"]:.3f} |')
    fine = data['contours'][levels[-1]]
    raw_w = mp.mpc(*fine['raw_W'])
    baseline = json.loads((ROOT/'results/pii_first/results.json').read_text())
    initial_j = matrix(data['monitor']['0']['J'])
    kappa = []
    for t in data['points']:
        jac = matrix(data['monitor'][str(t)]['J'])
        f = matrix(data['reference']['F'][str(t)])
        kappa.append(2*max(map(abs,jac))*max(map(abs,f))/max(map(abs,initial_j)))
    residuals = data['finite_difference_residual']['relative_by_step']
    calibration = sum(v['seconds'] for v in data['rk_trials'].values())
    text = f'''# Пенлеве-II: первые результаты сравнения

Расчёт от 15 сентября 2026 года. Постановка, формулы и смысл циклов:
[PII_METHOD_RU.md](PII_METHOD_RU.md). Полные данные:
[results.json](results/pii_comparison/results.json).

## Интервал и точность

Однородное PII, u(-1)=0.2, u'(-1)=0.1. Интервал x от -1 до -13;
контрольные точки -1, -2, -4, -7, -10, -13. Оба метода используют
70-значную арифметику и общий нелинейный фон. Независимый монитор Стокса
вычислен с 80 значащими цифрами.

E есть максимум относительной ошибки нормированной фундаментальной матрицы
на шести контрольных точках; D есть максимум относительного дрейфа
J(x)F(x)-J(-1). Нормы определены в методической записи. Максимумы ошибок
согласованы в пределах 10%; дрейф при подборе допусков не использовался.

| Уровень | Метод | E | D | Ошибка вронскиана | Время, с |
| --- | --- | --- | --- | --- | --- |
{chr(10).join(rows)}

Ошибка вронскиана есть максимум модуля det F - 1.
Время относится к одному выбранному запуску; общий фон, опорный расчёт
и монитор исключены. Стоимость содержащегося в общем фоне интеграла от u
отдельно не выделена. Время уровня 3 и его RK-сопоставления сохранено
из завершённой части отдельного калибровочного запуска.
Сумма времён всех сохранённых пробных запусков RK: {calibration:.2f} с.

| Уровень | E_RK / E_контур | D_RK / D_контур | Время контура / время RK |
| --- | --- | --- | --- |
{chr(10).join(ratios)}

Отношение дрейфов больше единицы означает меньший дрейф у контура;
отношение времён больше единицы означает более быстрый RK.

![Ошибка и дрейф на контрольных точках](results/pii_comparison.png)

Линии соединяют измеренные точки и не задают оценки между ними.
Точка x=-1, где F=I по нормировке, в логарифмические графики не включена.

## Независимые проверки

Повторные опорные расчёты с 50 и 70 значащими цифрами согласовались по F
до {number(data['reference']['refinement_F'])}, по u в абсолютной норме
до {number(data['reference']['refinement_u_absolute'])}.
Остаточный дрейф J(x)F_ref(x)-J(-1):
{number(data['monitor_reference_variation_drift'])}.
Абсолютный дрейф самих четырёх коэффициентов Стокса:
{number(data['monitor_stokes_drift_absolute'])}.

При x=-13 увеличение радиуса спектрального усечения с 5 до 5.5,
порядка асимптотики с 64 до 80 и уточнение спектрального продолжения
изменили J относительно на
{number(data['monitor_refinement_at_minus13']['J_relative'])}.
Эти результаты существенно ниже ошибок сравниваемых решений.

Вронскиан двух ненормированных контурных решений при x=-1:
W = {mp.nstr(raw_w.real,12)} {float(raw_w.imag):+.11f} i,
его модуль {float(abs(raw_w)):.8f}. Обращение начальной матрицы невырождено
в выполненном расчёте; интервального доказательства этой численной оценки нет.

Пятиузловая разностная проверка уравнения по контурным значениям при x=-7:
шаг 0.001 даёт невязку {number(residuals['0.001'])},
шаг 0.0005 даёт {number(residuals['0.0005'])}.
Уменьшение примерно в 16 раз согласуется с четвёртым порядком формулы.
Дополнительно проверены значение и производная точного интеграла Эйри
при u=0; этот вырожденный фон не используется в таблице сравнения.

![Фон, два решения и два цикла](results/pii_solutions_and_contours.png)

## Контроль квадратуры

Первоначальный выбор шага учитывал только коэффициенты спектральных
столбцов. При внутреннем допуске 1e-12 максимальная ошибка решения
составляла {number(baseline['contours']['1e-12']['max_solution_error'])}.
Включение рядов обоих накопленных интегралов в тот же механизм выбора
шага уменьшило её до {number(data['contours']['1e-12']['max_solution_error'])}.
Время контурного построения изменилось с
{baseline['contours']['1e-12']['seconds']:.2f} до {data['contours']['1e-12']['seconds']:.2f} с.
Начальные данные, радиус, порядок асимптотики и рабочая арифметика сохранены.
Это результат уточнения конкретного алгоритма квадратуры, а не сравнение
при одинаковой достигнутой ошибке. Старые данные сохранены отдельно.

## Вывод для общего препринта

Контурная формула PII дала два независимых решения и прошла проверки
по опорному решению, уравнению и вариациям монодромии. На трёх уровнях
дрейф у контура меньше в 1.2--1.3 раза; большого выигрыша на этом
регулярном фоне не обнаружено.
При самом точном из сопоставленных уровней контурное построение оказалось
быстрее RK45; при менее строгой точности его дополнительные затраты существенны.
Времена однократные и не устанавливают переносимую границу эффективности.
Спектральное продолжение и квадратура используют ряды 32-го порядка,
а прямой метод использует схему RK пятого порядка. Поэтому результат
по времени включает влияние разных порядков алгоритмов. Сравнение с
более высокими порядками RK в той же многозначной арифметике не выполнено.

Максимальное значение коэффициента
2 ||J(x)||_max ||F_ref(x)||_max / ||J(-1)||_max на сетке равно
{float(max(kappa)):.3f}. Неравенство D(x) <= kappa(x) E(x) + ошибка монитора
поясняет связь ошибок решения с дрейфом. Направление матричной ошибки также
влияет на дрейф; одинаковые максимумы E не задают одинакового распределения
ошибок по x.

Для PIV ранее получены отношения дрейфов RK/контур около 1.9 и 14 при близкой
ошибке решения: [EQUAL_ACCURACY_RU.md](EQUAL_ACCURACY_RU.md).
Эти числа относятся к другому фону и другим функциям монодромии. Их нельзя
сравнивать с абсолютным D для PII без учёта нормировки и обусловленности.

Предмет общего текста: зависимость эффективности контурного построения
линейных вариаций от спектральной структуры, режима решения и требуемой
точности. Два интегральных представления уже опубликованы автором;
потенциальный вклад нового текста состоит в вычислительном исследовании.
Для вывода об околополюсных режимах PII, нескольких фонах и других схемах RK
данных пока нет. Параметр PII, отличный от нуля, здесь не рассматривался.

Исходные статьи, журнальные архивы и прежние проверки не изменились:
контрольные суммы сверены после запуска.

## Воспроизведение

Из корня рабочей папки, с окружением из requirements-high-precision.txt:

```sh
python computational_preprint/compare_pii.py --output NEW_RESULT_DIRECTORY
python -m unittest discover -s computational_preprint -p 'test_pii.py' -v
python computational_preprint/build_pii_report.py
```

Последняя команда строит этот отчёт по зафиксированному набору
results/pii_comparison/results.json. Для нового набора нужно изменить путь
DATA в построителе. Все входные параметры и снимки вычислительных модулей
хранятся рядом с результатами. Неоконченные калибровки помечены STATUS.md
и в итоговую таблицу не включены; завершённый уровень 1e-12 из частичной
калибровки переиспользован с сохранением исходных времён.
'''
    (ROOT/'PII_COMPARISON_RU.md').write_text(text)
    print(ROOT/'PII_COMPARISON_RU.md')
    print(ROOT/'results/pii_comparison.png')
    print(ROOT/'results/pii_solutions_and_contours.png')


if __name__ == '__main__':
    main()
