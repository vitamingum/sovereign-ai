# utf8.ps1 - Set PowerShell UTF-8 encoding
#
#       . .\utf8.ps1
#       echo "test" | py remember opus -
#
#       or add to $PROFILE for permanent fix

$OutputEncoding = [System.Text.Encoding]::UTF8
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
[Console]::InputEncoding = [System.Text.Encoding]::UTF8

# Also set for chcp (code page)
chcp 65001 > $null

Write-Host "UTF-8 enabled" -ForegroundColor Green
