implement main
    open core, stdio

domains
    vault = rubles; dollars.

class facts - polyclinicDb
    карта_пациента : (integer PID, string FullNameP, string Address, string Number, integer Age, string Job).
    врач : (integer DID, string FullNameD, string Profile).
    приём : (integer DID, integer PID, string DateP, string Diagnosis, string Treatment, boolean SickDay).
    расписание_приемов : (integer DID, integer Start, integer End).
    лекарство : (string Medicine).
    метод_лечения : (string Method).
    выходные : (string Day).
    будние : (string Day).
    стоимость_приёма : (integer DID, integer PriceP, vault VP).
    стоимость_лекарства : (string Medicine, integer PriceM, vault VM).
    количество_таблеток : (string Medicine, integer Amount).
    время_терапии : (string Method, integer Days).
    стоимость_терапии : (string Method, integer PriceT, vault VT).
    таблетки_в_день : (string Medicine, integer TPD).
    длительность_таблеток : (string Medicine, integer Duration).

class predicates  %Вспомогательные предикаты
    длина : (A*) -> integer N.
    сумма : (real* List) -> real Sum.
    среднее : (real* List) -> real Average determ.

class facts
    s : (real Sum) single.
    стоимость : (string Med, integer Price, vault VT) nondeterm.

clauses
    s(0).
    длина([]) = 0.
    длина([_ | T]) = длина(T) + 1.

    сумма([]) = 0.
    сумма([H | T]) = сумма(T) + H.

    среднее(L) = сумма(L) / длина(L) :-
        длина(L) > 0.

class predicates
    %расписание_поликлиники : (string Day) nondeterm.
    история_болезней : (string PatientName) -> string* Бол determ.
    назначенное_лечение : (string PatientName) -> string* Леч determ.
    назначенные_препараты : (string PatientName) -> string* determ.
    общий_счёт : (string PatientName) -> real Счёт nondeterm.
    средний_возраст : (string DoctorName) -> real Возраст nondeterm.
    цена : (string C) nondeterm.
    выписанные_препараты : (string FullName) -> string* Таблетки determ.
    кол_преп : (string FullName) -> integer N determ.

clauses
    выписанные_препараты(X) = Med :-
        врач(ID, X, _),
        !,
        Med =
            [ Cure ||
                приём(ID, _, _, _, Cure, _),
                лекарство(Cure)
            ].

    кол_преп(X) = длина(выписанные_препараты(X)).

    цена(X) :-
        лекарство(X),
        стоимость_лекарства(X, Cost, _),
        assert(стоимость(X, Cost, rubles)),
        fail.
    цена(X) :-
        метод_лечения(X),
        стоимость_терапии(X, Cost, _),
        assert(стоимость(X, Cost, rubles)),
        fail.
    цена(X) :-
        приём(_, _, _, _, X, _).

    история_болезней(X) = History :-
        карта_пациента(ID, X, _, _, _, _),
        !,
        History = [ Dis || приём(_, ID, _, Dis, _, _) ].

    назначенное_лечение(X) = History :-
        карта_пациента(ID, X, _, _, _, _),
        !,
        History =
            [ Heal ||
                приём(_, ID, _, _, Heal, _),
                метод_лечения(Heal)
            ].

    назначенные_препараты(X) = History :-
        карта_пациента(ID, X, _, _, _, _),
        !,
        History =
            [ Heal ||
                приём(_, ID, _, _, Heal, _),
                лекарство(Heal)
            ].

    общий_счёт(X) =
            сумма(
                [ Price + Cost ||
                    приём(DID, ID, _, _, Heal, _),
                    стоимость_приёма(DID, Price, _),
                    цена(Heal),
                    стоимость(Heal, Cost, _)
                ]) :-
        карта_пациента(ID, X, _, _, _, _).

    средний_возраст(X) =
            среднее(
                [ Age ||
                    приём(DID, PID, _, _, _, _),
                    карта_пациента(PID, _, _, _, Age, _)
                ]) :-
        врач(DID, X, _).

clauses
    run() :-
        console::init(),
        file::consult("../polydb.txt", polyclinicDb),
        fail.

    run() :-
        X = 'Дымченко Дмитрий Юрьевич',
        L = общий_счёт(X),
        writef("Общий счёт пациента % составил %.", X, L),
        writef("\nПрепараты, назначенные пациенту % : %", X, назначенные_препараты(X)),
        nl,
        fail.

    run() :-
        X = 'Варлоков Михаил Евгеньевич',
        writef("Средний возраст пациентов у % равен\t", X),
        write(средний_возраст(X)),
        nl,
        fail.

    run() :-
        succeed.

end implement main

goal
    console::runUtf8(main::run).
