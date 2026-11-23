namespace OrbitCalculator

open System
open System.Text
open System.Threading
open Spectre.Console

type CalculatorState =
    { CurrentInput: string
      Result: string option
      Error: string option
      SqrtArmed: bool
      SqrtNumberOpen: bool
      LastAction: string option
      FlashFrames: int
      ShakeFrames: int
      PortalStep: int
      JustEvaluated: bool
      Running: bool }

module Expression =
    type private Expr =
        | Number of float
        | Unary of string * Expr
        | Binary of string * Expr * Expr
        | Function of string * Expr

    type private ParserState =
        { Text: string
          Index: int }

    let createOperation (op: string) : (float -> float -> float) =
        match op with
        | "+" -> fun left right -> left + right
        | "-" -> fun left right -> left - right
        | "*" -> fun left right -> left * right
        | "/" -> fun left right -> left / right
        | "^" -> fun left right -> Math.Pow(left, right)
        | _ -> fun _ _ -> Double.NaN

    let private skipSpaces state =
        let rec move index =
            if index < state.Text.Length && Char.IsWhiteSpace(state.Text.[index]) then
                move (index + 1)
            else
                { state with Index = index }

        move state.Index

    let private current state =
        if state.Index < state.Text.Length then Some state.Text.[state.Index] else None

    let private advance state =
        { state with Index = state.Index + 1 }

    let private isDigit character = character >= '0' && character <= '9'

    let private digitStringToFloat (digits: string) =
        digits
        |> Seq.fold (fun total digit -> total * 10.0 + float (int digit - int '0')) 0.0

    let private numberTokenToFloat (token: string) =
        let dotIndex = token.IndexOf('.')
        let wholeText, fractionText =
            if dotIndex < 0 then token, ""
            else token.Substring(0, dotIndex), token.Substring(dotIndex + 1)

        let wholeValue = if wholeText = "" then 0.0 else digitStringToFloat wholeText
        let fractionValue =
            if fractionText = "" then 0.0
            else digitStringToFloat fractionText / Math.Pow(10.0, float fractionText.Length)

        wholeValue + fractionValue

    let rec private parseExpression state =
        parseAdditive state

    and private parseAdditive state =
        parseMultiplicative state
        |> Result.bind (fun (left, afterLeft) -> parseAdditiveTail left afterLeft)

    and private parseAdditiveTail left state =
        let next = skipSpaces state

        match current next with
        | Some '+' ->
            parseMultiplicative (advance next)
            |> Result.bind (fun (right, afterRight) ->
                parseAdditiveTail (Binary("+", left, right)) afterRight)
        | Some '-' ->
            parseMultiplicative (advance next)
            |> Result.bind (fun (right, afterRight) ->
                parseAdditiveTail (Binary("-", left, right)) afterRight)
        | _ -> Ok(left, next)

    and private parseMultiplicative state =
        parseUnary state
        |> Result.bind (fun (left, afterLeft) -> parseMultiplicativeTail left afterLeft)

    and private parseMultiplicativeTail left state =
        let next = skipSpaces state

        match current next with
        | Some '*' ->
            parseUnary (advance next)
            |> Result.bind (fun (right, afterRight) ->
                parseMultiplicativeTail (Binary("*", left, right)) afterRight)
        | Some '/' ->
            parseUnary (advance next)
            |> Result.bind (fun (right, afterRight) ->
                parseMultiplicativeTail (Binary("/", left, right)) afterRight)
        | _ -> Ok(left, next)

    and private parseUnary state =
        let next = skipSpaces state

        match current next with
        | Some '+' ->
            parseUnary (advance next)
            |> Result.map (fun (value, afterValue) -> Unary("+", value), afterValue)
        | Some '-' ->
            parseUnary (advance next)
            |> Result.map (fun (value, afterValue) -> Unary("-", value), afterValue)
        | _ -> parsePower next

    and private parsePower state =
        parsePrimary state
        |> Result.bind (fun (left, afterLeft) ->
            let next = skipSpaces afterLeft

            match current next with
            | Some '^' ->
                parseUnary (advance next)
                |> Result.map (fun (right, afterRight) -> Binary("^", left, right), afterRight)
            | _ -> Ok(left, next))

    and private parsePrimary state =
        let next = skipSpaces state

        match current next with
        | Some character when isDigit character || character = '.' ->
            let rec scan index dotSeen =
                if index >= next.Text.Length then
                    index, dotSeen
                else
                    let character = next.Text.[index]
                    if isDigit character then scan (index + 1) dotSeen
                    elif character = '.' && not dotSeen then scan (index + 1) true
                    else index, dotSeen

            let finish, _ = scan next.Index false
            let token = next.Text.Substring(next.Index, finish - next.Index)
            let hasDigit = token |> Seq.exists isDigit

            if not hasDigit then
                Error "После десятичной точки должна идти цифра"
            else
                let value = numberTokenToFloat token
                Ok(Number value, { next with Index = finish })

        | Some '(' ->
            parseExpression (advance next)
            |> Result.bind (fun (inner, afterInner) ->
                let closing = skipSpaces afterInner
                match current closing with
                | Some ')' -> Ok(inner, advance closing)
                | _ -> Error "Пропущена закрывающая скобка ')'.")
        | Some '√' ->
            parseUnary (advance next)
            |> Result.map (fun (value, afterValue) -> Function("sqrt", value), afterValue)
        | Some character when Char.IsLetter(character) ->
            let rec scan index =
                if index < next.Text.Length && Char.IsLetter(next.Text.[index]) then scan (index + 1)
                else index

            let finish = scan next.Index
            let name = next.Text.Substring(next.Index, finish - next.Index).ToLowerInvariant()
            let afterName = skipSpaces { next with Index = finish }

            if name <> "sin" && name <> "cos" && name <> "tan" && name <> "tg" && name <> "sqrt" then
                Error $"Неизвестная функция '{name}'"
            else
                match current afterName with
                | Some '(' ->
                    parseExpression (advance afterName)
                    |> Result.bind (fun (argument, afterArgument) ->
                        let closing = skipSpaces afterArgument
                        match current closing with
                        | Some ')' ->
                            let normalizedName = if name = "tg" then "tan" else name
                            Ok(Function(normalizedName, argument), advance closing)
                        | _ -> Error $"Функции '{name}' требуется закрывающая скобка ')'")
                | _ -> Error $"Функция '{name}' должна сопровождаться '('"

        | None -> Error "Выражение неполное"
        | Some ')' -> Error "Присутствует лишняя закрывающая скобка"
        | Some character -> Error $"Лишний символ '{character}'"

    let private evaluate expression : float option * string option =
        let rec evaluateNode node =
            match node with
            | Number value ->
                if Double.IsFinite(value) then Some value, None
                else None, Some "Число выходит за пределы допустимого диапазона"

            | Unary("+", inner) -> evaluateNode inner
            | Unary("-", inner) ->
                match evaluateNode inner with
                | Some value, _ -> Some(-value), None
                | None, error -> None, error
            | Unary(_, _) -> None, Some "Неизвестная унарная операция"

            | Binary(operator, left, right) ->
                match evaluateNode left, evaluateNode right with
                | (Some leftValue, _), (Some rightValue, _) ->
                    if operator = "/" && rightValue = 0.0 then
                        None, Some "Деление на ноль невозможно"
                    else
                        let value = createOperation operator leftValue rightValue
                        if Double.IsFinite(value) then Some value, None
                        else None, Some "Операция не имеет конечного вещественного результата"
                | (_, Some error), _ -> None, Some error
                | _, (_, Some error) -> None, Some error
                | _ -> None, Some "Выражение не удалось вычислить"

            | Function(name, argument) ->
                match evaluateNode argument with
                | None, error -> None, error
                | Some value, _ ->
                    match name with
                    | "sqrt" ->
                        if value < 0.0 then None, Some "Квадратный корень из отрицательного числа невозможен"
                        else Some(Math.Sqrt(value)), None
                    | "sin" ->
                        let radians = value * Math.PI / 180.0
                        Some(Math.Sin(radians)), None
                    | "cos" ->
                        let radians = value * Math.PI / 180.0
                        Some(Math.Cos(radians)), None
                    | "tan" ->
                        let radians = value * Math.PI / 180.0
                        if abs (Math.Cos(radians)) < 1.0e-12 then
                            None, Some "При этом угле тангенс не определен"
                        else
                            Some(Math.Tan(radians)), None
                    | _ -> None, Some $"Неизвестная функция '{name}'"

        evaluateNode expression

    let tryEvaluate (text: string) : float option * string option =
        let initial = { Text = text; Index = 0 }

        match parseExpression initial with
        | Error error -> None, Some error
        | Ok(expression, afterExpression) ->
            let remaining = skipSpaces afterExpression
            if remaining.Index < text.Length then
                None, Some $"Неожиданные входные данные рядом с '{text.Substring(remaining.Index)}'."
            else
                let value, error = evaluate expression
                match value, error with
                | Some number, None ->
                    let rounded = Math.Round(number, 10, MidpointRounding.AwayFromZero)
                    let normalized = if abs rounded < 1.0e-10 then 0.0 else rounded
                    Some normalized, None
                | _ -> None, error

module Calculator =
    let initialState =
        { CurrentInput = ""
          Result = None
          Error = None
          SqrtArmed = false
          SqrtNumberOpen = false
          LastAction = None
          FlashFrames = 0
          ShakeFrames = 0
          PortalStep = 6
          JustEvaluated = false
          Running = true }

    let private clearFeedback state =
        { state with Error = None; Result = None; PortalStep = 6; ShakeFrames = 0 }

    let private finishSqrt state =
        if state.SqrtNumberOpen then
            { state with CurrentInput = state.CurrentInput + ")"; SqrtNumberOpen = false }
        else state

    let private withAction action state =
        { state with LastAction = Some action; FlashFrames = 5; Error = None; Result = None; PortalStep = 6 }

    let private prepareForTyping state =
        if state.JustEvaluated then
            { state with CurrentInput = ""; Result = None; Error = None; JustEvaluated = false; SqrtArmed = false; SqrtNumberOpen = false }
        else state

    let private prepareForContinuation state =
        if state.JustEvaluated then
            { state with Result = None; Error = None; JustEvaluated = false; PortalStep = 6; ShakeFrames = 0 }
        else
            clearFeedback state

    let private appendDigit digit state =
        let prepared = prepareForTyping state |> clearFeedback
        let next =
            if prepared.SqrtArmed then
                { prepared with
                    CurrentInput = prepared.CurrentInput + "√(" + string digit
                    SqrtArmed = false
                    SqrtNumberOpen = true }
            elif prepared.SqrtNumberOpen then
                { prepared with CurrentInput = prepared.CurrentInput + string digit }
            else
                let trimmed = prepared.CurrentInput.TrimEnd()
                let prefix = if trimmed.EndsWith(")", StringComparison.Ordinal) then trimmed + " * " else prepared.CurrentInput
                { prepared with CurrentInput = prefix + string digit }

        withAction (string digit) { next with JustEvaluated = false }

    let private isDigit character = character >= '0' && character <= '9'

    let private currentNumberToken (input: string) =
        let trimmed = input.TrimEnd()
        let rec findStart index =
            if index >= 0 && (isDigit trimmed.[index] || trimmed.[index] = '.') then findStart (index - 1)
            else index + 1

        if trimmed.Length = 0 || not (isDigit trimmed.[trimmed.Length - 1] || trimmed.[trimmed.Length - 1] = '.') then
            "", trimmed.Length
        else
            let start = findStart (trimmed.Length - 1)
            trimmed.Substring(start), start


    let private appendDecimal state =
        let prepared = prepareForTyping state |> clearFeedback
        let next =
            if prepared.SqrtArmed then
                { prepared with CurrentInput = prepared.CurrentInput + "sqrt(0."; SqrtArmed = false; SqrtNumberOpen = true }
            elif prepared.SqrtNumberOpen then
                let token, _ = currentNumberToken prepared.CurrentInput
                if token.Contains('.') then prepared else { prepared with CurrentInput = prepared.CurrentInput + "." }
            else
                let token, _ = currentNumberToken prepared.CurrentInput
                if token <> "" then
                    if token.Contains('.') then prepared else { prepared with CurrentInput = prepared.CurrentInput + "." }
                else
                    let trimmed = prepared.CurrentInput.TrimEnd()
                    let prefix = if trimmed.EndsWith(")", StringComparison.Ordinal) then trimmed + " * " else prepared.CurrentInput
                    { prepared with CurrentInput = prefix + "0." }

        withAction "." { next with JustEvaluated = false }

    let private appendOperator operator state =
        let prepared = prepareForContinuation state
        if prepared.SqrtArmed then
            { prepared with Error = Some "Введите число после √ прежде чем выбрать оператор"; LastAction = Some operator; FlashFrames = 5 }
        else
            let closed = finishSqrt prepared
            let trimmed = closed.CurrentInput.TrimEnd()
            let endsWithOperator =
                trimmed.Length > 0 && ([| '+'; '-'; '*'; '/'; '^' |] |> Array.contains trimmed.[trimmed.Length - 1])

            let baseText =
                if endsWithOperator then trimmed.Substring(0, trimmed.Length - 1).TrimEnd()
                else trimmed

            let newText =
                if baseText = "" && operator <> "-" then operator + " "
                elif baseText = "" then "-"
                else baseText + " " + operator + " "

            withAction operator { closed with CurrentInput = newText; SqrtNumberOpen = false; JustEvaluated = false }

    let private appendFunction name state =
        let prepared = prepareForContinuation state
        if prepared.SqrtArmed then
            { prepared with Error = Some "Введите число или сначала отмените режим √"; LastAction = Some name; FlashFrames = 5 }
        else
            let closed = finishSqrt prepared
            let trimmed = closed.CurrentInput.TrimEnd()
            let prefix =
                if trimmed = "" then ""
                elif trimmed.EndsWith(")", StringComparison.Ordinal) || (trimmed.Length > 0 && (isDigit trimmed.[trimmed.Length - 1] || trimmed.[trimmed.Length - 1] = '.')) then
                    trimmed + " * "
                else closed.CurrentInput

            withAction name { closed with CurrentInput = prefix + name + "("; JustEvaluated = false }

    let private toggleSqrt state =
        let prepared = prepareForTyping state |> clearFeedback
        if prepared.SqrtNumberOpen then
            withAction "√" (finishSqrt prepared)
        else
            withAction "√" { prepared with SqrtArmed = not prepared.SqrtArmed }

    let private toggleSign state =
        let prepared = prepareForContinuation state

        if prepared.SqrtArmed then
            withAction "+/-" { prepared with CurrentInput = prepared.CurrentInput + "√(-"; SqrtArmed = false; SqrtNumberOpen = true }
        else
            let token, start = currentNumberToken prepared.CurrentInput
            if token = "" then
                let trimmed = prepared.CurrentInput.TrimEnd()
                let canStartNegative =
                    trimmed = ""
                    || trimmed.EndsWith("(", StringComparison.Ordinal)
                    || (trimmed.Length > 0 && ([| '+'; '-'; '*'; '/'; '^' |] |> Array.contains trimmed.[trimmed.Length - 1]))

                if canStartNegative then
                    withAction "+/-" { prepared with CurrentInput = trimmed + "-" }
                else
                    withAction "+/-" prepared
            else
                let trimmed = prepared.CurrentInput.TrimEnd()
                let minusIndex = start - 1
                let rec previousNonSpace index =
                    if index >= 0 && Char.IsWhiteSpace(trimmed.[index]) then previousNonSpace (index - 1)
                    else index

                let contextIndex = previousNonSpace (minusIndex - 1)
                let hasUnaryMinus =
                    minusIndex >= 0
                    && trimmed.[minusIndex] = '-'
                    && (contextIndex < 0 || ([| '+'; '-'; '*'; '/'; '^'; '(' |] |> Array.contains trimmed.[contextIndex]))

                let changed =
                    if hasUnaryMinus then trimmed.Remove(minusIndex, 1)
                    else trimmed.Insert(start, "-")

                withAction "+/-" { prepared with CurrentInput = changed }

    let private appendOpenParen state =
        let prepared = prepareForTyping state |> clearFeedback
        let closed = finishSqrt prepared
        let trimmed = closed.CurrentInput.TrimEnd()
        let prefix =
            if trimmed = "" then ""
            elif trimmed.EndsWith(")", StringComparison.Ordinal) || (trimmed.Length > 0 && (isDigit trimmed.[trimmed.Length - 1] || trimmed.[trimmed.Length - 1] = '.')) then
                trimmed + " * "
            else closed.CurrentInput

        withAction "(" { closed with CurrentInput = prefix + "("; JustEvaluated = false }

    let private appendCloseParen state =
        let prepared = prepareForTyping state |> clearFeedback
        let closed = finishSqrt prepared
        withAction ")" { closed with CurrentInput = closed.CurrentInput + ")"; JustEvaluated = false }

    let private backspace state =
        let prepared = clearFeedback state
        if prepared.SqrtArmed then
            withAction "⌫" { prepared with SqrtArmed = false }
        elif prepared.CurrentInput.Length = 0 then
            withAction "⌫" prepared
        else
            let nextInput = prepared.CurrentInput.Substring(0, prepared.CurrentInput.Length - 1)
            let rootIsOpen = nextInput.LastIndexOf("√(", StringComparison.Ordinal) > nextInput.LastIndexOf(")", StringComparison.Ordinal)
            withAction "⌫" { prepared with CurrentInput = nextInput; SqrtNumberOpen = rootIsOpen; JustEvaluated = false }

    let effectiveExpression state =
        if state.SqrtNumberOpen then state.CurrentInput + ")" else state.CurrentInput

    let validationError state =
        if state.SqrtArmed then Some "РЕЖИМ √ АКТИВИРОВАН, ВВЕДИТЕ ЧИСЛО" 
        elif state.CurrentInput.Trim() = "" then Some "ВВЕДИТЕ ВЫРАЖЕНИЕ"
        else
            let expression = effectiveExpression state
            let _, error = Expression.tryEvaluate expression
            error

    let private evaluate state =
        if state.JustEvaluated then state
        else
            let prepared = clearFeedback state

            match validationError prepared with
            | Some error ->
                { prepared with Error = Some error; ShakeFrames = 8; PortalStep = 0; LastAction = Some "="; FlashFrames = 5 }
            | None ->
                let expression = effectiveExpression prepared
                match Expression.tryEvaluate expression with
                | Some value, None ->
                    let resultText =
                        if abs value < 1.0e-10 then "0"
                        else value.ToString("0.##########", Globalization.CultureInfo.InvariantCulture)

                    { prepared with
                        CurrentInput = expression
                        Result = Some resultText
                        Error = None
                        SqrtArmed = false
                        SqrtNumberOpen = false
                        JustEvaluated = true
                        PortalStep = 0
                        LastAction = Some "="
                        FlashFrames = 5 }
                | _, Some error ->
                    { prepared with Error = Some error; ShakeFrames = 8; PortalStep = 0; LastAction = Some "="; FlashFrames = 5 }
                | _ ->
                    { prepared with Error = Some "Выражение не удалось вычислить"; ShakeFrames = 8; PortalStep = 0 }

    let clear state =
        withAction "AC" { initialState with Running = state.Running; LastAction = Some "AC"; FlashFrames = 5 }

    let handleKey (key: ConsoleKeyInfo) state =
        if key.Key = ConsoleKey.Escape || key.Key = ConsoleKey.Delete then
            clear state
        elif key.Key = ConsoleKey.Backspace then
            backspace state
        elif key.Key = ConsoleKey.Enter || key.KeyChar = '=' then
            evaluate state
        elif key.KeyChar >= '0' && key.KeyChar <= '9' then
            appendDigit key.KeyChar state
        else
            match key.KeyChar with
            | '.' -> appendDecimal state
            | '+' -> appendOperator "+" state
            | '-' -> appendOperator "-" state
            | '*' | 'x' | 'X' -> appendOperator "*" state
            | '/' -> appendOperator "/" state
            | '^' -> appendOperator "^" state
            | '(' -> appendOpenParen state
            | ')' -> appendCloseParen state
            | 'r' | 'R'  -> toggleSqrt state
            | 's' | 'S' -> appendFunction "sin" state
            | 'c' | 'C' -> appendFunction "cos" state
            | 't' | 'T' -> appendFunction "tan" state
            | 'n' | 'N' -> toggleSign state
            | 'a' | 'A' -> clear state
            | 'q' | 'Q' -> { state with Running = false }
            | _ -> state

    let tick state =
        { state with
            FlashFrames = max 0 (state.FlashFrames - 1)
            ShakeFrames = max 0 (state.ShakeFrames - 1) }

module View =
    type private Button =
        { Id: string
          Label: string
          Kind: string }

    let private centerMarkup width (value: string) =
        let visible =
            System.Text.RegularExpressions.Regex.Replace(value, @"\[[^\]]*\]", "")
        let left = max 0 ((width - visible.Length) / 2)
        String.replicate left " " + value
    let private centerBlock width (value: string) =
        value.Split('\n')
        |> Array.map (fun line -> centerMarkup width line)
        |> String.concat "\n"

    let private buttonRows =
        [ [ { Id = "7"; Label = "7"; Kind = "digit" }
            { Id = "8"; Label = "8"; Kind = "digit" }
            { Id = "9"; Label = "9"; Kind = "digit" }
            { Id = "√"; Label = "√"; Kind = "operator" }
            { Id = "sin"; Label = "sin"; Kind = "operator" } ]
          [ { Id = "4"; Label = "4"; Kind = "digit" }
            { Id = "5"; Label = "5"; Kind = "digit" }
            { Id = "6"; Label = "6"; Kind = "digit" }
            { Id = "*"; Label = "×"; Kind = "operator" }
            { Id = "cos"; Label = "cos"; Kind = "operator" } ]
          [ { Id = "1"; Label = "1"; Kind = "digit" }
            { Id = "2"; Label = "2"; Kind = "digit" }
            { Id = "3"; Label = "3"; Kind = "digit" }
            { Id = "-"; Label = "−"; Kind = "operator" }
            { Id = "tan"; Label = "tg"; Kind = "operator" } ]
          [ { Id = "0"; Label = "0"; Kind = "digit" }
            { Id = "."; Label = "."; Kind = "utility" }
            { Id = "+/-"; Label = "+/−"; Kind = "utility" }
            { Id = "+"; Label = "+"; Kind = "operator" }
            { Id = "="; Label = "="; Kind = "equals" } ]
          [ { Id = "^"; Label = "xʸ"; Kind = "operator" }
            { Id = "/"; Label = "÷"; Kind = "operator" }
            { Id = "("; Label = "("; Kind = "utility" }
            { Id = ")"; Label = ")"; Kind = "utility" }
            { Id = "AC"; Label = "AC"; Kind = "clear" } ] ]

    let private digits: Map<string, string list> =
        [ "0", [ "01110"; "10001"; "10001"; "10001"; "01110" ]
          "1", [ "00100"; "01100"; "00100"; "00100"; "01110" ]
          "2", [ "11110"; "00010"; "00100"; "01000"; "11111" ]
          "3", [ "11110"; "00010"; "00100"; "00010"; "11110" ]
          "4", [ "10010"; "10010"; "11111"; "00010"; "00010" ]
          "5", [ "11111"; "10000"; "11110"; "00001"; "11110" ]
          "6", [ "01110"; "10000"; "11110"; "10001"; "01110" ]
          "7", [ "11111"; "00001"; "00010"; "00100"; "01000" ]
          "8", [ "01110"; "10001"; "01110"; "10001"; "01110" ]
          "9", [ "01110"; "10001"; "01111"; "00001"; "01110" ] ]
        |> Map.ofList

    let private starLine width frame lane =
        [ 0 .. width - 1 ]
        |> List.map (fun column ->
            let drifted = (column + frame / 3 + lane * 7) % width
            if drifted % 19 = 0 then "[bold #FFF2C6]✦[/]"
            elif drifted % 13 = 0 then "[#F6B8FF].[/]"
            elif drifted % 9 = 0 then "[#A78BFA]*[/]"
            else " ")
        |> String.concat ""
    let private verticalStarLine (offset: int) =
        [| 0 .. 50 |]
        |> Array.map (fun i ->
            let pos = (i + offset) % 15
            if pos = 0 then "[bold #FFF2C6]✦[/]"
            elif pos = 5 then "[#F6B8FF].[/]"
            elif pos = 10 then "[#A78BFA]*[/]"
            else " ")
        |> String.concat "\n"

    let private padCell (text: string) =
        let trimmed = if text.Length > 5 then text.Substring(0, 5) else text
        let left = (5 - trimmed.Length) / 2
        let right = 5 - trimmed.Length - left
        " " + String.replicate left " " + trimmed + String.replicate right " " + " "

    let private pixelColor row =
        if row = 0 then "#55E8FF"
        elif row = 1 then "#279CDB"
        else "#15558F"

    let private renderButtonCell state valid button row =
        let isFlashing = state.FlashFrames > 0 && state.LastAction = Some button.Id
        let baseLine =
            match button.Kind with
            | "digit" ->
                let pattern = digits.[button.Label].[row]
                pattern
                |> Seq.mapi (fun column pixel ->
                    if pixel = '1' then
                        let color = if column = 4 && row > 3 then "#0A477D" else pixelColor row
                        $"[bold {color}]█[/]"
                    else " ")
                |> String.concat ""
                |> fun art -> " " + art + " "
            | _ ->
                if row <> 2 then String.replicate 7 " "
                else
                    let color =
                        match button.Kind with
                        | "operator" -> "#FFB04A"
                        | "equals" when valid -> "#FF63D8"
                        | "equals" -> "#596273"
                        | "clear" -> "#F78CFA"
                        | _ -> "#8DDCFF"
                    let label = padCell button.Label
                    $"[bold {color}]{label}[/]"

        if isFlashing then $"[on #173B63]{baseLine}[/]" else baseLine

    let private renderKeypad state valid =
        let horizontalBorder left middle right =
            left + (List.replicate 5 (String.replicate 7 "─") |> String.concat middle) + right

        let top = horizontalBorder "┌" "┬" "┐"
        let separator = horizontalBorder "├" "┼" "┤"
        let bottom = horizontalBorder "└" "┴" "┘"

        let renderedRows =
            buttonRows
            |> List.mapi (fun rowIndex row ->
                let cellRows = row |> List.map (fun button -> [ 0 .. 4 ] |> List.map (renderButtonCell state valid button))
                let artLines =
                    [ 0 .. 4 ]
                    |> List.map (fun lineIndex ->
                        let cells = cellRows |> List.map (fun lines -> lines.[lineIndex]) |> String.concat "│"
                        "│" + cells + "│")
                if rowIndex < 4 then artLines @ [ separator ] else artLines)
            |> List.concat

        [ top ] @ renderedRows @ [ bottom ] |> String.concat "\n"

    let private inputPanel state frame =
        let width = 54
        let border = "╭" + String.replicate (width - 2) "─" + "╮"
        let expression =
            if state.CurrentInput = "" then "      · нажмите любую клавишу, чтобы начать·"
            else Calculator.effectiveExpression state

        let cursor = if frame % 10 < 6 then "[bold #FFFFFF]▋[/]" else "[#5B6A82]▏[/]"
        let plainAvailable = 49
        let visible = if expression.Length > plainAvailable then "…" + expression.Substring(expression.Length - plainAvailable + 1) else expression
        let safe = Markup.Escape(visible)
        let spaces = String.replicate (max 0 (plainAvailable - visible.Length)) " "
        let body = "│ [bold #75F5FF]" + safe + "[/]" + spaces + cursor + " │"

        "\n"
        + "[bold #FF63D8]" + border + "[/]\n"
        + "[bold #FF63D8]" + body + "[/]\n"
        + "[bold #FF63D8]" + border.Replace("╭", "╰").Replace("╮", "╯") + "[/]"

    let private portal state frame =

        let scale = max 1 (min 6 (state.PortalStep + 1))
        let glow = if scale >= 5 then "#FF70DC" else "#A66BFF"
        let portalWidth = 32 + (scale * 2)
        let insideWidth = portalWidth - 4

        let leftPadding = String.replicate (max 0 ((56 - portalWidth) / 2)) " "

        let line1, line2 =
            let rawText =
                match state.Error, state.Result with
                | Some error, _ -> error
                | None, Some result -> result
                | _ -> 
                    match Calculator.validationError state with 
                    | Some msg -> msg 
                    | None -> "◉  ГОТОВО ◉"
            let isAlert = 
                state.Error.IsSome 
                || state.SqrtArmed 
                || (state.CurrentInput.Trim() <> "" && Calculator.validationError state |> Option.isSome)
            let alertColor = if state.SqrtArmed then "#FFB04A" else "#FF78B8"
            let maxLength = insideWidth
            let text1, text2 =
                if rawText.Length > maxLength then
                    let mutable idx = maxLength
                    while idx > 0 && rawText.[idx] <> ' ' do idx <- idx - 1
                    let splitIndex = if idx = 0 then maxLength else idx
                    (rawText.Substring(0, splitIndex).TrimEnd(), rawText.Substring(splitIndex).TrimStart())
                else
                    (rawText, "")

            let formatLine (text: string) =
                let textLength = text.Length
                let left = max 0 ((insideWidth - textLength) / 2)
                let right = max 0 (insideWidth - textLength - left)
                let colorStart = if isAlert then $"[bold {alertColor}]" else "[bold #52F7FF]"
                "[on #092C42] " + String.replicate left " " + colorStart + Markup.Escape(text) + "[/]" + String.replicate right " " + " [/]"
            (formatLine text1, formatLine text2)

        let baseWave = "≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈∿≈"
        let shift = frame % baseWave.Length
        let waveStr = baseWave.Substring(shift) + baseWave.Substring(0, shift)
        let wavePadding = String.replicate (max 0 ((portalWidth - waveStr.Length)/ 2)) " " + " "    
        
        let upper = leftPadding + wavePadding + $"[bold {glow}]{waveStr}[/]"
        let top = leftPadding + "[bold #63DFFF]╭" + String.replicate (insideWidth + 2) "─" + "╮[/]"
        let emptyLine = leftPadding + "[bold #63DFFF]│[/]" + "[on #092C42] " + String.replicate (insideWidth) " " + " [/]" + "[bold #63DFFF]│[/]"
        let middle1 = leftPadding + "[bold #63DFFF]│[/]" + line1 + "[bold #63DFFF]│[/]"
        let middle2 = leftPadding + "[bold #63DFFF]│[/]" + line2 + "[bold #63DFFF]│[/]"
        let lower = leftPadding + "[bold #63DFFF]╰" + String.replicate (insideWidth + 2) "─" + "╯[/]"
        let lowerWave = leftPadding + wavePadding + $"[bold {glow}]{waveStr}[/]"
        upper + "\n" + top + "\n" + emptyLine + "\n" + middle1 + "\n" + middle2 + "\n" + lower + "\n" + lowerWave

    let render state frame =
        let validation = Calculator.validationError state
        let valid = validation.IsNone
        let shake = if state.ShakeFrames > 0 && state.ShakeFrames % 2 = 0 then "   " else " "
        let starsTop = starLine 56 frame 0
        let starsBottom = starLine 56 (frame + 9) 2
        let leftStars = (verticalStarLine (frame / 2)).Split('\n')
        let rightStars = (verticalStarLine ((frame / 2) + 3)).Split('\n')
        let input = inputPanel state frame |> centerBlock 56
        let result = portal state frame
        let keypad = renderKeypad state valid |> centerBlock 56

        
        let centerContent =
            String.concat "\n"
                [ "[bold #E8E8FF]" + starsTop + "[/]"
                  shake + input
                  ""
                  "                 [bold #D38BFF]✦  КВАНТОВЫЙ ПОРТАЛ  ✦[/]"
                  result
                  ""
                  keypad
                  "[bold #E8E8FF]" + starsBottom + "[/]"
                  "   [#8792B5]Подсказки: 0–9 · + − * / ^ · s=sin c=cos t=tg · r=√[/]"
                  "                  [#8792B5] n=± · Enter== · Esc=AC · q=выйти[/]" ]

        let zipLines (left: string[]) (center: string) (right: string[]) =
            let cLines = center.Split('\n')
            cLines
            |> Array.mapi (fun i line ->
                let l = if i < left.Length then left.[i] else " "
                let visibleLength = System.Text.RegularExpressions.Regex.Replace(line, @"\[[^\]]*\]", "").Length
                let paddedLine = line + String.replicate (max 0 (57 - visibleLength)) " "
                
                let r = if i < right.Length then right.[i] else " "
                l + paddedLine + r)
            |> String.concat "\n"

        let body = zipLines leftStars centerContent rightStars
        let panel = Panel(Markup(body))
        panel.Header <- PanelHeader("")
        panel.Border <- BoxBorder.Double
        panel.BorderStyle <- Style(Color.Purple)
        panel.Padding <- Padding(0, 0)
        panel.Width <- 58

        panel.Expand <- false
        Align.Center(panel)

module Animation =
    let expandPortal (context: LiveDisplayContext) state frame =
        let rec animate step =
            if step > 6 then
                { state with PortalStep = 6 }
            else
                let glitchFrames = [| "░▒▓  СИГНАЛ ПОТЕРЯН  ▓▒░"; "0x7F?? / SYNC"; "≈≈  ВОССТАНОВЛЕНИЕ  ≈≈"; "···  ОТКРЫТИЕ ПОРТАЛА  ···" |]
                let withGlitch =
                    if step < glitchFrames.Length && state.Result.IsSome then
                        { state with Result = Some glitchFrames.[step]; PortalStep = step }
                    else
                        { state with PortalStep = step }

                context.UpdateTarget(View.render withGlitch (frame + step))
                Thread.Sleep(55)
                animate (step + 1)

        animate 0

    let shakeError (context: LiveDisplayContext) state frame =
        let rec animate step =
            if step <= 0 then { state with ShakeFrames = 0; PortalStep = 6 }
            else
                let animated = { state with ShakeFrames = step; PortalStep = 0 }
                context.UpdateTarget(View.render animated (frame + step))
                Thread.Sleep(42)
                animate (step - 1)

        animate 8

module Program =
    let rec private mainLoop (context: LiveDisplayContext) state frame =
        if not state.Running then
            ()
        else
            let nextState =
                if Console.KeyAvailable then
                    let key = Console.ReadKey(true)
                    let updated = Calculator.handleKey key state

                    if key.Key = ConsoleKey.Enter || key.KeyChar = '=' then
                        if updated.Error.IsSome then Animation.shakeError context updated frame
                        elif updated.Result.IsSome then Animation.expandPortal context updated frame
                        else updated
                    else
                        updated
                else
                    Calculator.tick state

            context.UpdateTarget(View.render nextState frame)
            Thread.Sleep(65)
            mainLoop context (Calculator.tick nextState) (frame + 1)

    [<EntryPoint>]
    let main _ =
    
        if Console.IsInputRedirected then
            AnsiConsole.MarkupLine("[bold red]Orbit Calculator требует интерактивный терминал[/]")
            1
        else
            Console.OutputEncoding <- Encoding.UTF8
            Console.CursorVisible <- false

            try
                let initial = Calculator.initialState
                let live = AnsiConsole.Live(View.render initial 0)
                live.AutoClear <- false
                live.Start(fun context -> mainLoop context initial 0) |> ignore

                Console.CursorVisible <- true
                AnsiConsole.MarkupLine("[bold #52F7FF]Сигнал завершен. Безопасных путешествий[/]")
                0
            with ex ->
                Console.CursorVisible <- true
                AnsiConsole.MarkupLine($"[bold red]Неожиданно завершенная сессия консоли: {ex.GetType().Name} - {ex.Message}[/]")
                1
