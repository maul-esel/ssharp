# The MIT License (MIT)
# 
# Copyright (c) 2014-2017, Institute for Software & Systems Engineering
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.
#
# Sources:
#    * https://www.nunit.org/index.php?p=guiCommandLine&r=2.4
#    * https://www.nunit.org/index.php?p=nunit-console&r=2.4
#    * https://msdn.microsoft.com/en-us/powershell/scripting/getting-started/cookbooks/managing-current-location
#    * https://msdn.microsoft.com/en-us/powershell/reference/5.1/microsoft.powershell.management/start-process
#    * https://www.safaribooksonline.com/library/view/windows-powershell-cookbook/9780596528492/ch11s02.html
#    * http://www.get-blog.com/?p=82

# Note: You must run the following command first
#  Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
# To Undo
#  Set-ExecutionPolicy -ExecutionPolicy Restricted -Scope CurrentUser

$nunit = "$PSScriptRoot\NUnit2\nunit-console.exe"
$binary = "$PSScriptRoot\SafetySharp.CaseStudies.RobotCell.dll"
$tmp_dir = "$PSScriptRoot\tmp"
$output_dir = "\\MASTER\data\SOPerformance"
$controllers=@("Centralized", "Coalition")

$env:Path += ";$PSScriptRoot\NUnit2"

New-Item -ItemType directory -Path $tmp_dir -Force

Foreach ($controller in $controllers) {
	ExecuteModelTypeTests $controller
	ExecuteFaultTypeTests $controller
	# TODO: move results from $tmp_dir to $output_dir or new subdirectory of it
}

function ExecuteModelTypeTests($controller) {
	$arguments = @("/labels", "/config:Release", "/include:ModelTypeTests_$controller", $binary)
	$stderr = "modeltypetests.$controller.err"
	$stdout = "modeltypetests.$controller.out"
	Start-Process -FilePath $nunit -ArgumentList $arguments -WorkingDirectory $tmp_dir -NoNewWindow -RedirectStandardError $stderr -RedirectStandardOutput $stdout -Wait
}

function ExecuteFaultTypeTests($controller) {$arguments = @("/labels", "/config:Release", "/include:FaultTypeTests_$controller", $binary)
	$stderr = "faulttypetests.$controller.err"
	$stdout = "faulttypetests.$controller.out"
	Start-Process -FilePath $nunit -ArgumentList $arguments -WorkingDirectory $tmp_dir -NoNewWindow -RedirectStandardError $stderr -RedirectStandardOutput $stdout -Wait
}