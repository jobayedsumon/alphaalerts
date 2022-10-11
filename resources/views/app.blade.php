<!DOCTYPE html>
<html lang="{{ str_replace('_', '-', app()->getLocale()) }}">
    <head>
        <meta charset="utf-8">
        <meta name="viewport" content="width=device-width, initial-scale=1">

        <link rel="icon" href="{{ asset('images/logo.png') }}" type="image/x-icon"/>

        <title>Alpha Alerts</title>

        <link href="https://use.fontawesome.com/releases/v5.15.1/css/all.css" rel="stylesheet" />

        <link rel="stylesheet" href="{{ asset('css/app.css') }}">

        <link rel="stylesheet" href="{{ asset('css/custom.css') }}">

        <!-- Include Frontend Application (webpack mix) -->
        <script defer src="{{asset('js/manifest.js')}}"></script>
        <script defer src="{{asset('js/vendor.js')}}"></script>
        <script defer src="{{asset('js/app.js')}}"></script>
    </head>
    <body>
        <div id="root"></div>
    </body>
</html>
