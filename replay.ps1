# Keeps exact submitted files intact and stages equivalent standalone modules.
param(
    [ValidateSet('All', 'Certificates', 'Refutations', 'Nagura', 'Analytic')]
    [string]$Suite = 'All'
)

$ErrorActionPreference = 'Stop'

$version = & lean --version
if ($LASTEXITCODE -ne 0 -or "$version" -notmatch '\b4\.33\.1\b') {
    throw 'Replay requires Lean 4.33.1 on PATH.'
}

function Copy-StandaloneModule {
    param([string]$Source, [string]$Module)

    Copy-Item -LiteralPath (Join-Path $PSScriptRoot $Source) -Destination "${Module}.lean"
}

function Copy-NetworkModule {
    param([string]$Source, [string]$Module, [string[]]$Imports)

    $text = [IO.File]::ReadAllText((Join-Path $PSScriptRoot $Source))
    $opening = [regex]::Match($text, '\Aimport Mathlib\r?\nimport Nodes[^\r\n]+\.Context\r?\n')
    if (!$opening.Success) {
        throw "Unexpected network import block in $Source"
    }

    $header = $Imports.ForEach({ "import $_" }) -join "`n"
    $local = $header + "`n" + $text.Substring($opening.Length)
    [IO.File]::WriteAllText((Join-Path $PWD "${Module}.lean"), $local)
}

function Invoke-KernelReplay {
    param([string]$Module)

    Write-Host "Building $Module"
    & lean -j 2 -M 3072 -DmaxHeartbeats=1000000 -o "${Module}.olean" "${Module}.lean"
    if ($LASTEXITCODE -ne 0) { throw "Lean build failed for $Module" }

    Write-Host "Replaying $Module"
    & leanchecker -v $Module
    if ($LASTEXITCODE -ne 0) { throw "Lean kernel replay failed for $Module" }
}

$build = Join-Path $PSScriptRoot '.lean-replay'
New-Item -ItemType Directory -Path $build -Force | Out-Null
$previousLeanPath = $env:LEAN_PATH
$env:LEAN_PATH = if ($previousLeanPath) {
    $build + [IO.Path]::PathSeparator + $previousLeanPath
} else {
    $build
}

Push-Location -LiteralPath $build
try {
    if ($Suite -in 'All', 'Certificates') {
        $primeImports = @('Mathlib.Data.Nat.Prime.Defs', 'Lean')
        Copy-NetworkModule 'certificates/erdos-849/short/Proof.lean' 'Erdos849Short' $primeImports
        Copy-NetworkModule 'certificates/erdos-849/long/Proof.lean' 'Erdos849Long' $primeImports
        Invoke-KernelReplay 'Erdos849Short'
        Invoke-KernelReplay 'Erdos849Long'
    }

    if ($Suite -in 'All', 'Refutations') {
        $finsetImports = @(
            'Mathlib.Algebra.BigOperators.Group.Finset.Defs'
            'Mathlib.Data.Finset.Card'
            'Mathlib.Data.Nat.Prime.Defs'
        )
        Copy-NetworkModule 'certificates/erdos-257/interval/Proof.lean' 'Erdos257Interval' $finsetImports
        Copy-NetworkModule 'certificates/erdos-257/product/Proof.lean' 'Erdos257Product' $finsetImports
        Invoke-KernelReplay 'Erdos257Interval'
        Invoke-KernelReplay 'Erdos257Product'
    }

    if ($Suite -in 'All', 'Nagura') {
        foreach ($module in @('Finite', 'Arithmetic', 'FactorialBounds', 'Valuations', 'NaguraBound')) {
            Copy-StandaloneModule "formalizations/nagura/${module}.lean" $module
            Invoke-KernelReplay $module
        }
    }

    if ($Suite -in 'All', 'Analytic') {
        foreach ($module in @('CheckCutoff', 'SexticTailBudget', 'SexticTailJoinPilot', 'SexticLowZeros')) {
            Copy-StandaloneModule "analysis/erdos-849/${module}.lean" $module
            Invoke-KernelReplay $module
        }
    }
} finally {
    Pop-Location
    $env:LEAN_PATH = $previousLeanPath
}
