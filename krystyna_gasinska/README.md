Prosty język imperatywny wzorowany na 'Latte'.
W języku występują typy char, int, bool, string.
Język oferuje zmienne, przypisywanie, literały, arytmetykę, porównania.
Dostępna jest pętla while i instrukcje warunkowe (if lub if-else).
Zmienne można przekazywać do funkcji przez wartość lub przez zmienną.
Dostępne są zmienne globalne.
Dostępne są wbudowane procedury print i print_line, które przyjmują
jeden argument typu string. Dzięki jawnemu rzutowaniu można wypisać
każdy typ (rzutować można typy dla których to ma sens, np char na int,
int na bool, wszystkie typy na string; np rzutowanie string na int nie ma sensu).
Procedury przyjmują argumenty ale nie zwracają wartości.
Język jest dynamicznie typowany. Ma statyczne wiązanie identyfikatorów.
Język zezwala na redeklarację zmiennych.
Zaimplementowana jest obsługa błędów wykonania. Komunikaty o błędach
wypisywane są na standardowe wyjście błędów.

Niestety język jest o wiele mniej ambitny niż planowałam na początku,
gdyż z niezależnych ode mnie przyczyn (grypa żołądkowa) miałam mniej czasu,
niż mi się wydawało. Jeśli byłaby taka możliwość, chciałabym dorobić
jeszcze kilka funkcjonalności w terminie czerwcowym.
Np. punkty 09, 11, 12, 18.

  Na 15 punktów
jest  01 (trzy typy)
jest  02 (literały, arytmetyka, porównania)
jest  03 (zmienne, przypisanie)
jest  04 (print)
jest  05 (while, if)
jest  06 (funkcje lub procedury, rekurencja)
jest  07 (przez zmienną / przez wartość / in/out)
      08 (zmienne read-only i pętla for)
      Na 20 punktów
jest  09 (przesłanianie i statyczne wiązanie)
jest  10 (obsługa błędów wykonania)
      11 (funkcje zwracające wartość)
      Na 30 punktów
      12 (4) (statyczne typowanie)
      13 (2) (funkcje zagnieżdżone ze statycznym wiązaniem)
      14 (1/2) (rekordy/listy/tablice/tablice wielowymiarowe)
      15 (2) (krotki z przypisaniem)
      16 (1) (break, continue)
      17 (4) (funkcje wyższego rzędu, anonimowe, domknięcia)
      18 (3) (generatory)

Dodatkowo: jawne rzutowanie

Razem: 18(?)
15
+1 obsługa błędów wykonania
+1 przesłanianie i statyczne wiązanie
+1 rzutowanie
