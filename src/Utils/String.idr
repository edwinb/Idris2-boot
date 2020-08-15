module Utils.String

%default total

export
stripQuotes : (str : String) -> { auto ok : length str `GTE` 2 } -> String
stripQuotes str = substr 1 (length str - 2) str
